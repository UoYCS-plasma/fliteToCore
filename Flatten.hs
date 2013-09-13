module Flatten where

import Syntax
import Monad
import Fresh

-- Flatten a possibly deeply-nested expression into a list of flat
-- bindings.  Assumes no case and lambda expressions present.

flatten :: Exp -> Fresh ([Binding], Exp)
flatten (App f xs) =
  do (bs, g) <- flat f
     (bss, ys) <- return unzip `ap` mapM flat xs
     return (bs ++ concat bss, App g ys)
flatten (PRSApp f xs) = 
  do (bss, ys) <- return unzip `ap` mapM flat xs
     return (concat bss, PRSApp f ys)
flatten (Let bs t) =
  do (cs, u) <-  flatten t
     bss <- mapM flattenB bs
     return (concat bss ++ cs, u)
flatten (Lam vs e) = error "flatten: unexpected lambda expression"
flatten (Case e as) = error "flatten: unexpected case expression"
flatten e = return ([], e)

flattenB (v, e) =
  do (bs, u) <- flatten e
     return (bs ++ [(v, u)])

flat (Int i) = return ([], Int i)
flat (Var v) = return ([], Var v)
flat (Con c) = return ([], Con c)
flat (Fun f) = return ([], Fun f)
flat e =
  do v <- fresh
     bs <- flattenB (v, e)
     return (bs, Var v)
