{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE CPP #-}

module Auxiliar (
    update,
    cont,
    r0,
    s0,
    ref',
    deref',
    (<+>),
    const',
    cond,
    lookup',
    filter,
    subscript,
    checkType,
    static,
    dynamic,
    getScope
    ) where

import Prelude hiding (error,seq,filter,undefined)
import Domains
import Debug.Trace

-- r0 --
r0 :: Env
r0 = \i -> Unbound

-- a0 --
s0 :: Store
s0 = (\l -> if (l == Level) then level else (if (l == New) then new else Unused))
  where level = (StoreSv (SvRv (BvNum (NumInt 1))))
        new = (StoreSv (SvRv (BvNum (NumInt 0))))

-- static :: scope --
static :: Scope
static (r,r') = r

-- dynamic :: scope --
dynamic :: Scope
dynamic (r,r') = r'

-- update --
class Update x y where
  (<+>) :: x -> y -> x

instance Update Store (Loc,Sv) where
  (<+>) s (Loc (_,a),v) = \l -> case l of 
                                      (Loc (_,a')) -> if (a == a')
                                                        then (StoreSv v)
                                                        else (s (Loc (Var,a')))
                                      otherwise -> s l
  (<+>) s (Input,v) = \l -> if (l == Input) then (StoreSv v) else (s l)
  (<+>) s (Output,v) = \l -> if (l == Output) then (StoreSv v) else (s l)
  
instance Update Env (Id,Dv) where
  (<+>) r (i,v) = r <+> (Id i,v)

instance Update Env (EnvId,Dv) where
  (<+>) r (i,v) = \i' -> if (i == i') then (EnvDv v) else (r i')

instance Update Env Env where
  (<+>) r r' = \i -> case (r' i) of
                     Unbound -> r i
                     d -> d

-- ref' --
ref' :: Q -> Ev -> Env -> Store -> Ans
ref' q e = new $ "Loc" ? (\l -> update l (\e' -> q (EvDv (DvLoc l))) e)

-- deref' --
deref' :: Q -> Ev -> Env -> Store -> Ans
deref' q e = case e of
              EvDv (DvLoc l) -> cont q l
              otherise -> q e

-- update --
update :: Loc -> Q -> Ev -> Env -> Store -> Ans
update l q e r s = case l of
                    Loc (Const,a) -> errorMsg ("Cannot update a const location.") undefined r s 
                    Loc (Var, a) -> toSv (\e' r' s'->q (EvBv Undefined) r' (s' <+> (l,e'))) e r s


-- cont --
cont :: Q -> Loc -> Env -> Store -> Ans
cont q l r s = case (s l) of
                Unused -> errorMsg ("Unused location: " ++ show l) undefined r s
                (StoreSv s') -> (?) "Ev" q s' r s

-- new --
new :: Q -> Env -> Store -> Ans
new q r s = case (r (Id "allocation")) of
              EnvDv (DvBv (BvString "heap")) -> q (locToEv (Var,(0, getNew s))) r (newStore s)
              otherwise -> q (locToEv (Var,(getLevel s, getNew s))) r (newStore s)
  where newStore s = \l -> if ( l == New) then newNew (s New) else s l
        newNew (StoreSv (SvRv (BvNum (NumInt i)))) = (StoreSv (SvRv (BvNum (NumInt (i + 1)))))
        getNew s = case (s New) of
                     (StoreSv (SvRv (BvNum (NumInt i)))) -> i
                     otherwise -> -1
        getLevel s = case (s Level) of
                     (StoreSv (SvRv (BvNum (NumInt i)))) -> i
                     otherwise -> -1
        locToEv l = (EvDv (DvLoc (Loc l)))

-- const' --
const' :: Loc -> Loc
const' (Loc (_,a)) = Loc (Const,a)

-- cond --
class Cond x where
  cond :: (x,x) -> Bool -> x
  cond (pX1,pX2) b = if b then pX1 else pX2

instance Cond Xd
instance Cond (Env -> Store -> Ans)
instance Cond (Store -> Ans)
instance Cond Ans

-- lookup' --
lookup' :: Id -> Env -> (Dv -> Env -> Store -> Ans) -> Store -> Ans
lookup' i r q s = case (r (Id i)) of
                    Unbound -> errorMsg ("Unbound identifier: " ++ show i ) undefined r s
                    (EnvDv d) -> q d r s

-- filter --
filter :: Env -> [Id] -> Env
filter r [] = r0
filter r (i:is) = case (r (Id i)) of
                    Unbound -> (filter r is)
                    EnvDv d -> case (r (Type i)) of
                                 Unbound -> (filter r is) <+> ((Id i),d)
                                 EnvDv t -> ((filter r is) <+> ((Id i),d)) <+> ((Type i),t)

-- subscript -- 
subscript :: Array -> Q -> Int -> Env -> Store -> Ans
subscript (Array (l,n1,n2)) q n r s = if (n >= n1 && n <= n2)
                                        then q (EvDv (DvLoc (l !! (n - n1)))) r s
                                        else errorMsg ("Array Index out of bounds: " ++ show n)
                                          undefined r s

-- checkType --
checkType :: Env -> Id -> String -> Ev
checkType r i t = case (r (Type i)) of
                    EnvDv (DvBv (BvString t)) -> (EvBv (BvBool True))
                    otherwise -> (EvBv (BvBool False))


-- getScope --
getScope :: Env -> Scope
getScope r = case (r (Id "scope")) of
               (EnvDv (DvScope s)) -> s
               otherwise -> static
