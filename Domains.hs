{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE CPP #-}

module Domains(
    Ans(AnsHalt,FlexibleAns),
    Result(RError,Stop),
    Error(Error),
    Id,
    Bv(BvNum,BvBool,BvString,BvChar,Undefined),
    Number(NumInt,NumShort,NumLong,NumByte,NumFloat,NumDouble),
    Rv,
    File(File),
    Array(Array),
    Dv(DvLoc, DvBv, DvQ, DvX, DvN, DvProc,DvArray,DvEnv,DvScope),
    EnvValue(EnvDv,Unbound),
    EnvId(Id,Type),
    Sv(SvRv,SvRec,SvArray,SvFile),
    StoreValue(StoreSv,Unused),
    Ev(EvBv,EvDv,EvEnv,EvArray,EvFile),
    Loc(Loc, Input, Output,Level,New),
    Access(Var,Const),
    Env,
    Store,
    Q,
    Pro,
    Cd,
    Ed,
    Ex,
    eval,
    evalList,
    Dd,
    Xd,
    Jd,
    For,
    Scope,
    Ad(Ad),
    Proc(Proc),
    Mode(Ref,Value,ValueAndResult,Constant,Name),
    Type,
    toSv,
    toEv,
    isSv,
    toBool,
    ImportOption(Opaque,Transparent),
    ExportOption(Visible,Encapsulated),
    error,
    errorMsg,
    undefined,
    (?),
    isByte,
    isInt,
    isShort,
    isLong,
    isDouble,
    isFloat,
    isChar,
    isString,
    isBool
        ) where

import Prelude hiding (error,undefined)
import Debug.Trace
import Data.Int

data Ans = AnsHalt (Result, Ev, Env, Store) | FlexibleAns (Ev, Env, Store) 
data Result = RError Error | Stop deriving (Eq,Show)
data Error = Error deriving (Eq,Show)
type Id = String
data Bv = BvNum Number | BvBool Bool | BvString String | BvChar Char | Undefined deriving (Eq,Show)
data Number = NumInt Int | NumLong Int64 | NumFloat Float | NumDouble Double
            | NumByte Int8 | NumShort Int16 deriving (Eq,Ord,Show)
data Array = Array ([Loc],Int,Int) deriving (Eq,Show)
data Dv = DvLoc Loc | DvBv Bv | DvQ (Ev -> Env -> Store -> Ans) | DvX (Env -> Q -> Store -> Ans)
        | DvN (Q -> Store -> Ans) | DvProc Proc | DvArray Array | DvEnv Env | DvScope Scope
data Sv = SvRv Rv | SvFile File | SvRec Env | SvArray Array deriving (Eq,Show)
type Rv = Bv
data File= File [Rv] deriving (Eq,Show)
data Ev = EvBv Bv | EvDv Dv | EvEnv Env | EvArray Array | EvFile File
data Loc = Loc (Access, Address) | Input | Output | Level | New deriving (Eq,Show)
type Address = (Int,Int)
data Access = Const | Var deriving (Eq,Show)
type Env = EnvId -> EnvValue
data EnvId = Id Id | Type Type deriving (Eq,Show)
data EnvValue = EnvDv Dv | Unbound deriving (Eq,Show)
type Store = Loc -> StoreValue
data StoreValue = StoreSv Sv | Unused deriving (Eq,Show)
type Q = Ev -> Env -> Store -> Ans
data Ad = Ad (Mode,Id)
data Mode = Ref | Value | ValueAndResult | Constant | Name deriving (Eq,Show)
data Proc = Proc ([Ad],Env -> Q -> [Ev] -> Store -> Ans)
type Type = String
type Class = Env
type Object = Env
type For = Env -> (Ev -> Cd) -> Q -> Store -> Ans

type Pro = File -> Env -> Store -> Ans 
type Ed = Env -> Q -> Store -> Ans 
type Cd = Env -> Q -> Store -> Ans 
type Dd = Env -> Q -> Store -> Ans 
type Xd = Env -> Q -> Store -> Ans 
-- Xd is used to refer to (Cd+Ed+Dd)
type Jd = Env -> Q -> Env
type Scope = (Env,Env) -> Env

-- Library options
data ImportOption = Transparent | Opaque [Id] deriving (Eq,Show)
data ExportOption = Visible | Encapsulated [Id] deriving (Eq,Show)

-- Class to unify Ed and Ev
class Show e => Ex e where
  eval :: e -> Ed
  evalList :: [e] -> Env -> ([Ev] -> Env -> Store -> Ans) -> Store -> Ans
  evalList e r q = evalList' [] e r q
    where evalList' es [] r q = q es r
          evalList' es (e':es') r q = eval e' r $ \e r' -> evalList' (es ++ [e]) es' r' q

instance Ex Ed where
  eval pE r q = \s -> pE r q s

instance Ex Ev where
  -- by name parameters
  eval (EvDv (DvN n)) r q = \s -> n q s
  -- values passed as expressions
  eval e r q = \s -> q e r s

-- Projection to Sv
class ToSv x where
  toSv :: (Sv -> Env -> Store -> Ans) -> x -> Env -> Store -> Ans

instance ToSv Ev where
  toSv q (EvBv b) r s = q (SvRv b) r s
  toSv q (EvDv (DvBv b)) r s = q (SvRv b) r s
  toSv q (EvEnv r') r s = q (SvRec r') r s
  toSv q (EvArray a) r s = q (SvArray a) r s
  toSv q e r s = errorMsg ("Cannot cast " ++ show e ++ " to Sv.") undefined r s


-- Injection to Ev
class ToEv x where
  toEv :: (Ev -> Env -> Store -> Ans) -> x -> Env -> Store -> Ans

instance ToEv Bv where
  toEv q b = q (EvBv b)

instance ToEv Dv where
  toEv q d = q (EvDv d)

instance ToEv Loc where
  toEv q l = q (EvDv (DvLoc l))

instance ToEv Ev where
  toEv q = q

instance ToEv EnvValue where
  toEv q (EnvDv d) r s = toEv q d r s
  toEv q _ r s = error undefined r s


-- Projection to Bool --
class ToBool x where
  toBool :: (Bool -> Env -> Store -> Ans) -> x -> Env -> Store -> Ans

instance ToBool Bv where
  toBool q (BvBool b) r s = q b r s
  toBool q _ r s = error undefined r s

instance ToBool Ev where
  toBool q (EvBv b) r s = toBool q b r s
  toBool q _ r s = error undefined r s

instance ToBool Dv where
  toBool q (DvBv b) r s = toBool q b r s
  toBool q _ r s = error undefined r s

-- Arithmetic Operations
instance Num Number where
  (NumByte b1) + (NumByte b2) = NumByte (b1 + b2)
  (NumInt b1) + (NumInt b2) = NumInt (b1 + b2)
  (NumShort b1) + (NumShort b2) = NumShort (b1 + b2)
  (NumLong b1) + (NumLong b2) = NumLong (b1 + b2)
  (NumDouble b1) + (NumDouble b2) = NumDouble (b1 + b2)
  (NumFloat b1) + (NumFloat b2) = NumFloat (b1 + b2)
  (NumByte b1) - (NumByte b2) = NumByte (b1 - b2)
  (NumInt b1) - (NumInt b2) = NumInt (b1 - b2)
  (NumShort b1) - (NumShort b2) = NumShort (b1 - b2)
  (NumLong b1) - (NumLong b2) = NumLong (b1 - b2)
  (NumDouble b1) - (NumDouble b2) = NumDouble (b1 - b2)
  (NumFloat b1) - (NumFloat b2) = NumFloat (b1 - b2)
  (NumByte b1) * (NumByte b2) = NumByte (b1 * b2)
  (NumInt b1) * (NumInt b2) = NumInt (b1 * b2)
  (NumShort b1) * (NumShort b2) = NumShort (b1 * b2)
  (NumLong b1) * (NumLong b2) = NumLong (b1 * b2)
  (NumDouble b1) * (NumDouble b2) = NumDouble (b1 * b2)
  (NumFloat b1) * (NumFloat b2) = NumFloat (b1 * b2)
  b1 * b2 = NumInt 0
  abs (NumByte b) = NumByte (abs b)
  abs (NumInt b) = NumInt (abs b)
  abs (NumShort b) = NumShort (abs b)
  abs (NumLong b) = NumLong (abs b)
  abs (NumDouble b) = NumDouble (abs b)
  abs (NumFloat b) = NumFloat (abs b)
  negate (NumByte b) = NumByte (negate b)
  negate (NumInt b) = NumInt (negate b)
  negate (NumShort b) = NumShort (negate b)
  negate (NumLong b) = NumLong (negate b)
  negate (NumDouble b) = NumDouble (negate b)
  negate (NumFloat b) = NumFloat (negate b)
  signum (NumByte b) = NumByte (signum b)
  signum (NumInt b) = NumInt (signum b)
  signum (NumShort b) = NumShort (signum b)
  signum (NumLong b) = NumLong (signum b)
  signum (NumDouble b) = NumDouble (signum b)
  signum (NumFloat b) = NumFloat (signum b)
  fromInteger b = NumInt (fromInteger b)

instance Num Bv where
  (BvNum b1) + (BvNum b2) = BvNum (b1 + b2)
  _ + _ = Undefined
  (BvNum b1) - (BvNum b2) = BvNum (b1 - b2)
  _ - _ = Undefined
  (BvNum b1) * (BvNum b2) = BvNum (b1 * b2)
  _ * _ = Undefined
  abs (BvNum b) = BvNum (abs b)
  abs _= Undefined
  negate (BvNum b) = BvNum (negate b)
  negate _= Undefined
  signum (BvNum b) = BvNum (signum b)
  signum _= Undefined
  fromInteger b = BvNum (fromInteger b)

instance Num Dv where
  (DvBv b1) + (DvBv b2) = DvBv (b1 + b2)
  _ + _ = DvBv Undefined
  (DvBv b1) - (DvBv b2) = DvBv (b1 - b2)
  _ - _ = DvBv Undefined
  (DvBv b1) * (DvBv b2) = DvBv (b1 * b2)
  _ * _ = DvBv Undefined
  abs (DvBv b) = DvBv (abs b)
  abs _= DvBv Undefined
  negate (DvBv b) = DvBv (negate b)
  negate _= DvBv Undefined
  signum (DvBv b) = DvBv (signum b)
  signum _= DvBv Undefined
  fromInteger b = DvBv (fromInteger b)

instance Num Ev where
  (EvBv b1) + (EvBv b2) = EvBv (b1 + b2)
  (EvDv d1) + (EvDv d2) = EvDv (d1 + d2)
  _ + _ = EvBv Undefined
  (EvBv b1) - (EvBv b2) = EvBv (b1 - b2)
  (EvDv d1) - (EvDv d2) = EvDv (d1 - d2)
  _ - _ = EvBv Undefined
  (EvBv b1) * (EvBv b2) = EvBv (b1 * b2)
  (EvDv d1) * (EvDv d2) = EvDv (d1 * d2)
  _ * _ = EvBv Undefined
  abs (EvBv b) = EvBv (abs b)
  abs (EvDv d) = EvDv (abs d)
  abs _ = EvBv Undefined
  signum (EvBv b) = EvBv (signum b)
  signum (EvDv d) = EvDv (signum d)
  signum _ = EvBv Undefined
  negate (EvBv b) = EvBv (negate b)
  negate (EvDv d) = EvDv (negate d)
  negate _ = EvBv Undefined
  fromInteger b = EvBv (fromInteger b)

instance Fractional Number where
  recip (NumDouble x) =  NumDouble (1 / x)
  recip (NumFloat x)  =  NumFloat (1 / x)
  recip b             =  NumDouble 0
  (NumDouble x) / (NumDouble y) =  NumDouble (x * recip y)
  (NumFloat x) / (NumFloat y) =  NumFloat (x * recip y)
  (NumInt x) / (NumInt y) =  NumInt (x `div` y)
  (NumShort x) / (NumShort y) =  NumShort (x `div` y)
  (NumByte x) / (NumByte y) =  NumByte (x `div` y)
  (NumLong x) / (NumLong y) =  NumLong (x `div` y)
  fromRational x = (NumDouble (fromRational x))

instance Fractional Bv where
  recip (BvNum x) =  BvNum (recip x)
  recip b       =  BvNum (NumDouble 0)
  (BvNum x) / (BvNum y) =  BvNum (x / y)
  fromRational x = (BvNum (fromRational x))

instance Fractional Ev where
  recip (EvBv x) =  EvBv (recip x)
  recip e       =  EvBv (BvNum (NumDouble 0))
  (EvBv x) / (EvBv y) =  EvBv (x / y)
  fromRational x = EvBv (fromRational x)

-- Relational Operations

instance Ord Bv where
  compare (BvNum n1) (BvNum n2) = compare n1 n2
  compare (BvBool b1) (BvBool b2) = compare b1 b2
  compare (BvString s1) (BvString s2) = compare s1 s2
  compare _ _ = GT

instance Ord Dv where
  compare (DvBv b1) (DvBv b2) = compare b1 b2
  compare _ _ = GT

instance Ord Ev where
  compare (EvBv b1) (EvBv b2) = compare b1 b2
  compare (EvDv d1) (EvDv d2) = compare d1 d2
  compare _ _ = GT

instance Eq Ev where
  (EvBv b1) == (EvBv b2) = b1 == b2
  (EvDv d1) == (EvDv d2) = d1 == d2
  _ == _ = False
  (EvBv b1) /= (EvBv b2) = b1 /= b2
  (EvDv d1) /= (EvDv d2) = d1 /= d2
  _ /= _ = False

instance Show Ev where
  show (EvBv b) = "(EvBv " ++ show b ++ ")"
  show (EvDv d) = "(EvDv " ++ show d ++ ")"
  show (EvEnv r) = "(EvEnv)"
  show (EvArray (Array a)) = "(EvEnv " ++ show a ++ ")"
  show (EvFile f) = "(EvFile " ++ show f ++ ")"


instance Eq Dv where
  (DvBv b1) == (DvBv b2) = b1 == b2
  (DvLoc l1) == (DvLoc l2) = l1 == l2
  _ == _ = False
  (DvBv b1) /= (DvBv b2) = b1 /= b2
  (DvLoc l1) /= (DvLoc l2) = l1 /= l2

instance Show Dv where
  show (DvBv b) = "(DvBv " ++ show b ++ ")"
  show (DvLoc l) = "(DvLoc " ++ show l ++ ")"
  show (DvQ _) = "(DvQ ?)"
  show (DvX _) = "(DvQ X)"
  show (DvProc _) = "(DvProc ?)"
  show (DvArray a) = "(DvArray " ++ show a ++ ")"

instance Eq Env where
  r == r' = False

instance Show Env where
  show r = "(Env)"
-- Type Checking --
class IsSv t where
  isSv :: t -> Bool
  isSv _ = False

instance IsSv Bv where
  isSv _ = True

instance IsSv Ev where
  isSv (EvBv _) = True
  isSv _ = False

class TypeCheck t1 t2 where
  (?) :: String -> (t2 -> Env -> Store -> Ans) -> t1 -> Env -> Store -> Ans
  (?) _ q t r s = errorMsg "TypeCheck" undefined r s
 
instance TypeCheck Ev Loc where
  (?) "Loc" q (EvDv (DvLoc l)) = q l 

instance TypeCheck Ev Ev where
  (?) "Loc" q (EvDv (DvLoc l)) = q (EvDv (DvLoc l)) 
  (?) "Bv" q (EvBv b) = q (EvBv b) 
  (?) "Rv" q (EvBv b) = q (EvBv b) 
  (?) "Array" q (EvArray a) = q (EvArray a)
-- Check Bv internal types
  (?) "Bool" q (EvBv b) = (?) "Bool" (\b -> q (EvBv b)) b
  (?) "Num" q (EvBv b) =  (?) "Num" (\b -> q (EvBv b)) b
  (?) "String" q (EvBv b) =  (?) "String" (\b -> q (EvBv b)) b

instance TypeCheck Bv Bv where
  (?) "Bool" q (BvBool b) = q (BvBool b)
  (?) "Num" q (BvNum n) = q (BvNum n)
  (?) "String" q (BvString s) = q (BvString s)

instance TypeCheck Dv Dv where
  (?) "Loc" q (DvLoc l) = q (DvLoc l)
  (?) "Bv" q (DvBv b) = q (DvBv b)
  (?) "Q" q (DvQ q') = q (DvQ q')
  (?) "Xd" q (DvX a) = q (DvX a)
  (?) "Array" q (DvArray a) = q (DvArray a)

instance TypeCheck Dv Loc where
  (?) "Loc" q (DvLoc l) = q l

instance TypeCheck Dv Proc where
  (?) "Proc" q (DvProc p) = q p
  (?) "Fun" q (DvProc p) = q p

instance TypeCheck Ev Dv where
  (?) "Dv" q (EvBv b) = q (DvBv b)
  (?) "Loc" q (EvDv (DvLoc l)) = q (DvLoc l)
  (?) "Dv" q (EvDv (DvLoc l)) = q (DvLoc l)
  (?) "Array" q (EvDv (DvArray a)) = q (DvArray a)
  (?) "Dv" q (EvDv (DvArray a)) = q (DvArray a)
  (?) "Proc" q (EvDv (DvProc a)) = q (DvProc a)
  (?) "Fun" q (EvDv (DvProc a)) = q (DvProc a)
  (?) "Dv" q (EvDv (DvProc a)) = q (DvProc a)
  (?) n q t = \r s -> errorMsg ("Cannot cast " ++ show t ++ " to Dv as " ++ n ) undefined r s

instance TypeCheck Ev Env where
  (?) "Record" q (EvEnv r) r' s = q r r' s
  (?) "Class" q (EvEnv r) r' s = q r r' s
  (?) "Object" q (EvEnv r) r' s = q r r' s
  (?) _ q t r s = errorMsg ("Cannot cast " ++ show t ++ " to Ev") undefined r s

instance TypeCheck Ev Number where
  (?) "Num" q (EvBv (BvNum n)) = q n

instance TypeCheck Ev Int where
  (?) "Num" q (EvBv (BvNum (NumInt n))) = q n

instance TypeCheck Ev Bool where
  (?) "Num" q (EvBv (BvBool b)) = q b

instance TypeCheck Ev Array where
  (?) "Array" q (EvArray a) = q a

instance TypeCheck Ev Proc where
  (?) "Proc" q (EvDv d) = (?) "Proc" q d
  (?) "Fun" q (EvDv d) = (?) "Fun" q d

instance TypeCheck Sv Ev where
  (?) "Ev" q (SvFile f) = q (EvFile f)
  (?) "Ev" q (SvRv b) = q (EvBv b)
  (?) "Ev" q (SvRec r) = q (EvEnv r)
  (?) "Ev" q (SvArray a) = q (EvArray a)

instance TypeCheck Ev Rv where
  (?) "Rv" q (EvBv b) = q b
  (?) _ q t = errorMsg ("Cannot cast " ++ show t ++ " to Rv") undefined

isByte :: Ev -> Bool
isByte (EvBv (BvNum (NumByte _))) = True
isInt :: Ev -> Bool
isInt (EvBv (BvNum (NumInt _))) = True
isShort :: Ev -> Bool
isShort (EvBv (BvNum (NumShort _))) = True
isLong :: Ev -> Bool
isLong (EvBv (BvNum (NumLong _))) = True
isDouble :: Ev -> Bool
isDouble (EvBv (BvNum (NumDouble _))) = True
isFloat :: Ev -> Bool
isFloat (EvBv (BvNum (NumFloat _))) = True
isChar :: Ev -> Bool
isChar (EvBv (BvChar _)) = True
isString :: Ev -> Bool
isString (EvBv (BvString _)) = True
isBool :: Ev -> Bool
isBool (EvBv (BvBool _)) = True

-- error --
error :: Ev -> Env -> Store -> Ans
error e r s = trace ("Error ") (AnsHalt (RError Error, e, r, s))

errorMsg :: String -> Ev -> Env -> Store -> Ans
errorMsg m e r s = trace ("Error:" ++ m) (AnsHalt (RError Error, e, r, s))

undefined :: Ev
undefined = (EvBv Undefined)

-- Debug --
instance Show (Env -> Q -> Store -> Ans) where
  show e = "(Env -> Q -> Store -> Ans)"
