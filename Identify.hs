module Identify where

import Syntax
import Traversals
import Descend

-- Rewrites (Var n) to (Fun n) where n refers to a function.

identifyFuncs :: Prog -> Prog
identifyFuncs p =
  [Func f xs (fun (concatMap patVars xs) e) | Func f xs e <- p]
  where
    fs = funcs p

    fun vs (Case e as) =
      Case (fun vs e) [(p, fun (vs ++ patVars p) e) | (p, e) <- as]
    fun vs (Let bs e) = 
      let ws = vs ++ map fst bs
      in  Let [(v, fun ws e) | (v, e) <- bs] (fun ws e)
    fun vs (Lam ws e) = Lam ws (fun (vs++ws) e)
    fun vs (Var v) | v `elem` fs && v `notElem` vs = Fun v
    fun vs e = descend (fun vs) e
