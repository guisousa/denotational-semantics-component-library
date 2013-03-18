{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Components(
    run,
    pipe,
-- Commands
    skip,
    assign,
    output,
    resultIs,
    seq,
    call,
    loop,
--- Memory Management,
    alloc,
    deref,
    ref,
    const,
    push,
    pop,
--- Sequencers
    abort,
    throw,
    escape,
    catch,
    trap,
-- Expressions
    lookup,
    index,
    apply,
    valof,
    record,
    array,
--- Data Abstraction
    class0,
--- Types
    int,
    short,
    long,
    byte,
    float,
    double,
    char,
    string,
    bool,
-- Declarations
    accum,
    elabSeq,
    elabCol,
    elabRec,
-- Scope
    static,
    dynamic,
    useStaticScope,
    useDynamicScope,
-- Generic
    addEnv,
    choose,
-- Saltos
    addLabel,
    elab,
    -- elabSeq, 
    -- addEnv,
    jump,
-- Abstraction
    proc,
    makeClosure,
    makeAbstraction,
    bind,
    parametrize
    ) where

import Prelude hiding (const,error,seq,lookup,filter,undefined,catch)
import Debug.Trace
import Data.Int
import Domains
import Auxiliar hiding (static,dynamic)

-- run (Exp x Dec + Exp) -> Prog --
class Run r where
  run :: r -> Pro

instance Run Cd where
  run pC i r s = pC r q s''
    where s' = (s <+> (Input, SvFile i))
          s'' = (s' <+> (Output, SvFile (File [])))
          q = \e r s -> AnsHalt (Stop, e, r, s )

-- Commands -------------------------------------------------------------------
-- skip -> Cmd --
skip :: Cd
skip r q s = q (EvBv Undefined) r s

assign :: (Ex e1, Ex e2) => (e1,e2) -> Cd
assign (pE1,pE2) r q = eval pE1 r $ "Loc" ? (\l r' -> eval pE2 r' $ deref' $ "Rv" ? (update l q))
--assign (pE1,pE2) r q = \s -> (?) "Loc" (\(Loc l) -> q (EvBv Undefined)) (EvBv Undefined) r s

-- output (Ed) -> Cmd --
output :: (Ex e) => e -> Cd
output pE r q = cont (\o r -> eval pE r $ deref' $ "Rv" ? (\e r' s' -> q undefined r' (s' <+> (Output,output' o e)))) Output r
  where output' o e = case o of
                        EvFile (File f) -> SvFile (File (f ++ [e]))

class Seq s where
  seq :: (s,s) -> s

instance Seq Xd where
  seq (pX1,pX2) r q = pX1 r ( \e r' -> pX2 r' q)

resultIs :: Ex e => e -> Cd
resultIs pE r q = lookup' "resultIs" r $ \(DvQ q') r' -> eval pE r' $ deref' $ q'

call :: (Ex e1, Ex e2) => (e1,[e2]) -> Cd
call (pE1,pE2) r q = eval pE1 r $ \e r' -> case e of
                                             (EvDv (DvProc(Proc (a,p)))) -> evalPar (zip a pE2) p q r'
                                             (EvDv (DvX x)) -> x r' q
                                             otherwise -> errorMsg ("Trying to call something that is not a procedure.") undefined r'

class Loop l where
  loop :: l -> Cd

instance (Ex e1, Ex e2) => Loop (e1,Cd,e2) where
  loop (pE1,pC,pE2) = fix (\f -> choose(pE1, seq(pC, choose(pE2, f, skip)), skip))
    where fix f = f (fix f)

instance Ex e => Loop (e,Cd) where
  loop (pE,pC) = loop(pE, pC, bool("True"))

--Gera um erro de duplicata, porque nao e possivel distinguir entre Ed e Cd
--instance Loop (Cd,Ed) where
--  loop (pC,pE) = loop(bool("True"), pC, pE)

-- For --

class For' f where
  for :: f -> Xd

instance For' (Xd,Ed,Xd,Xd) where
  for (pX1,pE,pX2,pX3) = seq(accum(pX1), loop(pE, seq(pX3,pX2), bool("true")))

instance For' (Id, For, Cd) where
  for (pI,pF,pC) r q = accum(bind(pI, ref(undefined))) r $ \e r' -> pF r' (p pI) q
    where p i = \e -> assign(lookup(i), e)

singleStep :: Ex e => e -> For
singleStep pE r p q = eval pE r $ \e r' -> p e r' q 

while :: (Ex e1, Ex e2) => (e1,e2) -> For
while (pE1,pE2) = fix (\f r p q -> eval pE1 r $ \e r' -> eval pE2 r' $ deref' $ "Bool" ? (\b r'' -> if (b) then (p e r'' (\e r -> f r p q)) else ( q undefined r'')))
    where fix f = f (fix f)

range :: (Ex e1, Ex e2, Ex e3) => (e1,e2,e3) -> For
range (pE1,pE2,pE3) r p q = eval pE1 r $ "Num" ? \n1 r1 -> step (pE2,pE3) r1 p q n1
  where step (w2,w3) r p q n1 = eval w2 r $ "Num" ? \n2 r2 -> eval w3 r2 $ "Num" ? \n3 r3 -> if ((n1 - n3) * (signum n2) < 1)
                                                                                               then (p n1 r3 (\e r' -> step (w2,w3) r' p  q (n1 + n2)))
                                                                                               else (q undefined r3)

instance Seq For where
  seq (pF1,pF2) r p q = pF1 r p $ \e r' -> pF2 r' p q

-- Gerencia de Memoria
push e r q s = q e r (\l -> if (l == Level) then (getNextLevel s) else s l)
  where getLevel s = case (s Level) of
                     (StoreSv (SvRv (BvNum (NumInt i)))) -> i
                     otherwise -> -1
        getNextLevel s = (StoreSv (SvRv (BvNum (NumInt ((getLevel s) + 1)))))

pop e r q s =if ((getLevel s) == 1) then (errorMsg ("Already at bottom of stack") undefined r s) else  q e r (\l -> if (l == Level) then (getPreviousLevel s) else (case l of
                                                                                                                                                                       Loc (_,(n, _)) -> if (n == (getLevel s)) then Unused else ( s l)
                                                                                                                                                                       otherwise -> s l))
  where getLevel s = case (s Level) of
                     (StoreSv (SvRv (BvNum (NumInt i)))) -> i
                     otherwise -> -1
        getPreviousLevel s = (StoreSv (SvRv (BvNum (NumInt ((getLevel s) - 1)))))

alloc :: Ex e => e -> Ed
alloc pE r q = eval pE (r <+> ("allocation",(DvBv (BvString ("heap"))))) $ ref' $ (\e r' -> q e r)

deref :: Ex e => e -> Ed
deref pE r q = eval pE r $ deref' $ q

ref :: Ex e => e -> Ed
ref pE r q = eval pE r $ ref' $ q

const :: Ex e => e -> Ed
const pE r q = ref pE r $ "Loc" ? \l -> q (EvDv (DvLoc (const' l)))


-- Sequencers --
abort :: Cd
abort r q = errorMsg "Execution aborted" undefined r

class Escape e where
  escape :: e -> Cd

instance Escape (Cd, Id, Scope) where
  escape (pC, pI, scope) r q = pC (r <+> (pI, DvQ (\e r' -> q e (scope(r,r'))))) q

instance Escape (Cd, Id) where
  escape (pC, pI) r q = escape (pC, pI, getScope r) r q

throw :: Ex e => e -> Cd
throw pE r q = eval pE r $ \e r'-> lookup' "catch" r' $ \(DvProc (Proc (a,p))) r'' -> p r'' q [e]

class Catch c where
  catch :: c -> Cd

instance Catch (Cd, Proc, Scope) where
  catch (pC,pP, scope) r q = pC (r <+> ("catch",catch' pP scope r q)) q
    where catch' (Proc (a,p)) scope r q = DvProc (Proc (a, \r' q' -> p (scope(r,r')) q))

instance Catch (Cd, Proc) where
  catch (pC,pP) r q = catch (pC, pP, getScope r) r q

trap :: (Ex e1, Ex e2) => (e1,[(e2,Xd)],Xd) -> Xd
trap (pE,pL,pX) r q = case (unzip pL) of
                        (es,cs) -> evalList es r $ \es' r' -> eval pE r' $ deref' $ \e -> find e es' cs pX q
  where find e (e':es) (c:cs) x q r = deref' (\e'' r' -> if (e == e'') then  (c r' q) else (find e es cs x q r')) e' r
        find e [] [] x q r = x r q

-- Expressions ----------------------------------------------------------------
-- Basic Types --
int :: String -> Ed
int b r q = q (EvBv (BvNum (NumInt (read b :: Int)))) r
short :: String -> Ed
short b r q = q (EvBv (BvNum (NumShort (read b :: Int16)))) r
long :: String -> Ed
long b r q = q (EvBv (BvNum (NumLong (read b :: Int64)))) r
byte :: String -> Ed
byte b r q = q (EvBv (BvNum (NumByte (read b :: Int8)))) r
float :: String -> Ed
float b r q = q (EvBv (BvNum (NumFloat (read b :: Float)))) r
double :: String -> Ed
double b r q = q (EvBv (BvNum (NumDouble (read b :: Double)))) r
char :: String -> Ed
char b r q = q (EvBv (BvChar (read b :: Char))) r
string :: String -> Ed
string b r q = q (EvBv (BvString b)) r
bool :: String -> Ed
bool b r q = q (EvBv (BvBool (read b :: Bool))) r

-- Type Checking --
class GetType t where
  getType :: t -> Ed

instance GetType Id where
  getType pI r q = case (r (Type pI)) of
                     Unbound -> string("unknown") r q
                     (EnvDv d) -> q (EvDv d) r

instance GetType Ev where
  getType e r q = if (isByte e)
                    then string("byte") r q
                    else if (isShort e)
                           then string("short") r q
                           else if (isInt e)
                                  then string("int") r q
                                  else if (isLong e)
                                         then string("long") r q
                                         else if (isDouble e)
                                                then string("double") r q
                                                else if (isChar e)
                                                       then string("char") r q
                                                       else if (isString e)
                                                              then string("string") r q
                                                              else if (isBool e)
                                                                     then string("bool") r q
                                                                     else case (e) of
                                                                            (EvEnv o) -> case (o (Id "class")) of
                                                                                           (EnvDv d) -> q (EvDv d) r 
                                                                                           otherwise ->  string("unkown") r q
                                                                            otherwise -> string("unkown") r q 

class Lookup v where
  lookup :: v -> Ed

instance Lookup Id where
  lookup i r q = lookup' i r $ toEv $ q

instance Lookup (Id,Id) where
  lookup (pI1,pI2) r q = lookup pI1 r $ deref' $ "Record" ? (\e r' -> lookup pI2 e (\e' r'' -> q e' r))

instance Lookup (Ed,Id) where
  lookup (pE,pI) r q = eval pE r $ deref' $ "Record" ? (\e r' -> lookup pI e (\e' r'' -> q e' r))

instance Lookup (Ev,Id) where
  lookup (pE,pI) r q = eval pE r $ deref' $ "Record" ? (\e r' -> lookup pI e (\e' r'' -> q e' r))

class Index v where
  index :: v -> Ed

-- TODO: Aqui tambem dava conflito
instance Ex e => Index (e,Ed) where
  index (pE1,pE2) r q = eval pE1 r $ deref' $ "Array" ? (\a r' -> eval pE2 r' $ "Num" ? (subscript a q))

instance Ex e => Index (e,Ev) where
  index (pE1,pE2) r q = eval pE1 r $ deref' $ "Array" ? (\a r' -> eval pE2 r' $ "Num" ? (subscript a q))

-- apply (Ev* -> Ev + Error, Ed*) -> Ed
class Apply x where
  apply :: x -> Ed

instance Ex e => Apply ([Ev] -> Either Ev Error, [e]) where
  apply (o, es) r q = eval' es [] (\e' -> case (o e') of
                                              Left e -> toEv q e
                                              otherwise -> errorMsg ("Apply's operator failed with args:" ++ show es) undefined) r
    where eval' :: Ex e=> [e] -> [Ev] -> ([Ev] -> Env -> Store -> Ans) -> Env -> (Store -> Ans)
          eval' (e:es) e2s q r = eval e r $ deref' $ \v -> eval' es (e2s ++ [v]) q
          eval' [] e2s q r = q e2s r

instance Ex e => Apply (String, [e]) where
  apply ("+", es) = apply(intOp (+), es)
  apply ("-", es) = apply(intOp (-), es)
  apply ("*", es) = apply(intOp (*), es)
  apply ("/", es) = apply(intOp (/), es)
  apply ("=", es) = apply(boolOp (==), es)
  apply ("!=", es) = apply(boolOp (/=), es)
  apply (">", es) = apply(boolOp (>), es)
  apply ("<", es) = apply(boolOp (<), es)

instance Ex e => Apply (String, e, e) where
  apply (o,e1,e2) = apply(o, [e1,e2])

intOp :: (Ev -> Ev -> Ev) -> ([Ev] -> Either Ev Error)
intOp o = \e -> case o (e !! 0) (e !! 1) of
                  (EvBv Undefined) -> Right Error
                  e' -> Left e'

boolOp :: (Ev -> Ev -> Bool) -> ([Ev] -> Either Ev Error)
boolOp o = \e -> Left (EvBv (BvBool (o (e !! 0) (e !! 1))))

instance Ex e => Apply (Ed,[e]) where
  apply (pE1,pE2) r q = eval pE1 r $ "Fun" ? (\(Proc (a,f)) -> evalPar (zip a pE2) f q)

instance Ex e => Apply (Ev,[e]) where
  apply (pE1,pE2) r q = eval pE1 r $ "Fun" ? (\(Proc (a,f)) -> evalPar (zip a pE2) f q)

evalPar :: Ex e => [(Ad,e)] -> (Env -> Q -> [Ev] -> Store -> Ans) -> Q -> Env -> Store -> Ans
evalPar a p q r = evalPar' [] a ( \e r' -> p r' (\e' r''-> q e' r) e) r
  where evalPar' es ((Ad (m,i),e):as) q' = evalPar'' m e $ \e -> evalPar' (es ++ [e]) as q'
        evalPar' es [] q = q es
        evalPar'' Name e q r = q (EvDv (DvN (eval e r))) r
        evalPar'' _ e q r = eval e r q 

valof :: Cd -> Ed
valof pC r q = pC (r <+> ("resultIs", DvQ (\e r' -> q e r))) error

record :: (Dd) -> Ed
record (pD) r q = pD r $ \e r' -> q (EvEnv r') r

class Ex e => ClassArray e where
  array :: (e,e,[e]) -> Ed
  array (pE1,pE2,pE3) r q = eval pE1 r $ "Num" ? (\n1 r' -> eval pE2 r' $ "Num" ? (\n2 -> checkBoundaries n1 n2 $ \r'' s -> evalList pE3 r'' ( storeValues [] $ \l -> q (EvArray (Array (l,n1,n2)))) s))
    where checkBoundaries n1 n2 q' = if (n2 < n1)
                                      then (errorMsg ("Incorrect array boundaries: (" ++ show n1 ++ "," ++ show n2 ++ ")") undefined)
                                      else (if ((length pE3) <= (n2 - n1))
                                              then (errorMsg "Array boundaries and value size are incompatible") undefined
                                              else q')
          storeValues l q' [] = q' l
          storeValues l q' (e:es) = deref' (ref' $ "Loc" ? (\l' -> storeValues (l ++ [l']) q' es)) e

instance ClassArray Ed
instance ClassArray Ev

-- Data Abstraction --

class Class c where
  class0 :: c -> Ed

instance Class (Dd,Dd,Scope) where
  class0 (pDc,pDo,scope) r q = pDc r $ \e c -> q (EvEnv (c <+> ("class",DvEnv c) <+> ("constructor", constructor pDo scope r c))) r
    where constructor pDo scope r c = DvX (\r' -> pDo ((scope(r,r')) <+> c <+> ("class",DvEnv c)))

instance Class (Dd,Dd) where
  class0 (pDc,pDo) r q = class0 (pDc,pDo,getScope r) r q


subclass :: (Ex e1, Ex e2) => (e1,e2) -> Ed
subclass (pE1,pE2) r q = eval pE1 r $ "Class" ? (\c1 r' -> eval pE2 r' $ "Class" ? (\c2 -> q (EvEnv (c1 <+> (c2 :: Env) <+> ("constructor", constructor c1 c2)))))
  where constructor c1 c2 = DvX (\r q -> object(EvEnv c1) r $ "Object" ? \o1 r' -> object(EvEnv c2) (r' <+> o1) $ "Object" ? \o2 -> q (EvEnv (o1 <+> (o2 :: Env) <+> ("super", DvEnv o1))))

class Ex o => Object o where
  object :: o -> Ed
  object pE r q = eval pE r $ "Class" ? (\c r' -> construct c r' $ \e o -> q (EvEnv (c <+> o <+> ("this",DvEnv o))) r)
    where construct c r q = lookup' "constructor" c $ \(DvX d) c' -> d r q 

instance Object Ev
instance Object Ed

-- Declarations ---------------------------------------------------------------
-- accum(Dd) -> Dd --
accum :: Dd -> Dd
accum pD r q = pD r (\e r' -> q e (r <+> r'))

-- elabSeq(Dd,Dd) -> Dd --
class ElabSeq x where
  elabSeq :: (x,x) -> x
  
instance ElabSeq Dd where
  elabSeq (pD1,pD2) r q = pD1 r $ \e r1 -> pD2 (r <+> r1) $ \e' r2 -> q undefined (r <+> r1 <+> r2)

-- elabCol(Dd,Dd) -> Dd --
elabCol :: (Dd,Dd) -> Dd
elabCol (pD1,pD2) r q = pD1 r $ \e r1 -> pD2 r $ \e' r2 -> q undefined (r <+> r1 <+> r2)


-- elabRec(Dd,Dd) -> Dd --
class ElabRec x where
  elabRec :: x -> Dd

instance ElabRec Dd where
  elabRec (pD) r q = \s -> case (y s) of
                            (AnsHalt _) -> errorMsg "Single declaration of elabRec failed." undefined r s
                            (FlexibleAns (e,r',s')) -> q (EvBv Undefined) r' s'
    where y s = pD (r <+> (r'' s)) (\e r s -> (FlexibleAns (e,r,s))) s
          r'' s = case (y s) of
                    (AnsHalt _) -> r0
                    (FlexibleAns (e,r',s')) -> r'

instance ElabRec (Dd,Dd) where
  elabRec (pD1,pD2) = elabRec(elabCol(pD1,pD2))

-- useStaticScope --
useStaticScope :: Xd -> Xd
useStaticScope pX r q = pX (r <+> ("scope",DvScope static)) q

-- useDynamicScope --
useDynamicScope :: Xd -> Xd
useDynamicScope pX r q = pX (r <+> ("scope",DvScope dynamic)) q

static :: Scope
static (r,r') = r

dynamic :: Scope
dynamic (r,r') = r'

-- Generic --------------------------------------------------------------------
class AddEnv x where
  addEnv :: (x,Xd) -> Xd

instance AddEnv Dd where
  addEnv (pD,pX) r q = pD r $ \e r' -> pX r' q

choose :: Ex e => (e,Xd,Xd) -> Xd
choose (pE,pX1,pX2) r q = eval pE r $ deref' $ toBool $ \b r -> cond(pX1 r q, pX2 r q) b

-- Saltos ---------------------------------------------------------------------
instance AddEnv Jd where
  addEnv (pJ,pC) r q = pC (r <+> r') q
    where r' = pJ (r <+> r') q

class AddLabel a where
  addLabel :: a -> Jd

instance AddLabel (Id,Cd,Scope) where
  addLabel (pI,pC,scope) r q = r0 <+> (pI,DvQ (\e r' -> pC (scope(r,r')) q))

instance AddLabel (Id,Cd) where
  addLabel (pI,pC) r = addLabel(pI,pC,getScope r) r

skipLabel :: Jd
skipLabel r q  = r0

instance ElabSeq Jd where
  elabSeq (pJ1,pJ2) r q = r <+> r1 <+> r2
    where r1 = pJ1 r q
          r2 = pJ2 r q

elab :: (Jd,Cd) -> Jd
elab (pJ,pC) r q = pJ r (\e r' -> pC r' q)

jump :: Id -> Cd
jump pI r q = lookup' pI r $ \(DvQ q') r' -> q' (EvBv Undefined) r'

-- Abstracao ------------------------------------------------------------------

-- proc --
class Proc' p where
  proc :: p -> Ed

instance Proc' Xd where
  proc pX r q = q (EvDv (DvX pX)) r

instance Proc' Proc where
  proc pP r q = q (EvDv (DvProc pP)) r

instance Proc' (Xd, Scope) where
  proc (pX, scope) r q = q (EvDv (DvX (x' pX r))) r
    where x' x r = (\r' -> x (scope(r,r')))

instance Proc' (Proc, Scope) where
  proc (pP, scope) r q = q (EvDv (DvProc (p' pP r))) r
    where p' (Proc (a,p)) r = Proc (a, \r' -> p (scope(r,r')))

makeClosure :: (Dd,Xd) -> Xd
makeClosure (pD,pX) r q = pD r $ \e' r' -> pX r' $ \e'' r'' -> q e'' r

makeAbstraction :: (Xd,ImportOption, ExportOption) -> Xd
makeAbstraction (pX,pO1,pO2) r q = pX (imported pO1 r) $ \e r' -> q e (exported pO2 r')
  where imported Transparent r'' = r''
        imported (Opaque i) r'' = filter r'' i
        exported Visible r'' = r''
        exported (Encapsulated i) r'' = r <+> (filter r'' i)
                        
-- bind --
class Bind b where
  bind :: b -> Dd
  
instance Ex e => Bind (Id, e) where
  bind (pI, pE) r q = eval pE r $ "Dv" ? \d r' -> q undefined (r0 <+> (pI, f d pI :: Dv))
    where f (DvEnv e) pI = DvEnv (e <+> ("classname",  DvBv (BvString pI)))
          f d pI = d 
  
instance Ex e => Bind (Id, e, Type) where
  bind (pI, pE, pT) r q = bind(pI, pE) r $ \e r' -> q undefined (r' <+> (Type pI, (DvBv (BvString pT))))

parametrize :: ([Ad],Xd) -> Proc
parametrize (pA,pX) = Proc (pA,\r q v -> addPar (reverse (zip pA v)) pX r q)
  where addPar [] pX' = pX'
        addPar (y:ys) pX' = addPar ys (body y pX')
        body :: (Ad,Ev) -> (Env -> Q -> Store -> Ans) -> Env -> Q -> Store -> Ans
        body (Ad (m,i),e) pX' r' q' = entry m ("Dv" ? (\e' r'' -> pX' (r'' <+> (i,e')) (\e'' -> exit m e (q' e'') e'))) e r'

-- entry
entry :: Mode -> (Ev -> Env -> Store -> Ans) -> Ev -> Env -> Store -> Ans
entry Value q = deref' $ ref' $ q
entry ValueAndResult q = entry Value q
entry Ref q = "Loc" ? q
entry Constant q = deref' $ ref' $ "Loc" ? (\l -> q (EvDv (DvLoc (const' l))))
entry Name q = ref' $ q

-- exit
exit :: Mode -> Ev -> (Env -> Store -> Ans) -> Dv -> Env -> Store -> Ans
exit ValueAndResult e q e' = (?) "Loc" (\l -> (?) "Loc" (cont (update l (\e'' -> q))) e') e
exit _ _ q _ = q

-- pipe(Ed, Xd) --
pipe :: Ex e => (e, (Ev -> Xd)) -> Xd
pipe (pE,pX) r q = eval pE r $ \e r' -> pX e r' q

