module Main where

import Prelude hiding (exp)
import Domains
import Components
import Auxiliar

-- Abstract Syntax Tree

data Prog = PROG Exp
data Exp = SUM Exp Exp
         | SUB Exp Exp
         | MUL Exp Exp
         | DIV Exp Exp
         | NUM String

-- Semantic Equations

prog :: Prog -> File -> Ans 

prog (PROG e) input = run(exp e) input r0 s0

exp :: Exp -> Ed

exp (NUM n) = int(n)
exp (SUM e1 e2) = apply("+", exp e1, exp e2)
exp (SUB e1 e2) = apply("-", exp e1, exp e2)
exp (MUL e1 e2) = apply("*", exp e1, exp e2)
exp (DIV e1 e2) = apply("/", exp e1, exp e2)

-- Main Function

main = result (prog (parse) input)
  where result p = case p of
                     AnsHalt (Stop,e,r,s) -> print e
                     AnsHalt (RError Error,e,r,s) -> print Error
        input = File []

parse = example
  where example = PROG (SUM (NUM "1") (NUM "7"))
