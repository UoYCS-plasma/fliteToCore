module Reynolds where

import Syntax
import Descend
import Traversals
import List

apply :: Exp -> [Exp] -> Exp
apply f [] = f
apply f (e:es) = apply (App (Fun "@") [f, e]) es

-- Eliminate applications of variables.

varAppElim :: Prog -> Prog
varAppElim = onExp varApp
  where
    varApp (App (Var x) es) = apply (Var x) (map varApp es)
    varApp e = descend varApp e

-- Eliminate over-saturated applications.

overElim :: Prog -> Prog
overElim p = onExp over p
  where
    env = [(f, length args) | Func f args e <- p ]

    over (App (Fun f) es) =
      case lookup f env of
        Nothing -> App (Fun f) es'
        Just n  -> if   length es > n
                   then apply (App (Fun f) (take n es')) (drop n es')
                   else App (Fun f) es'
      where es' = map over es
    over e = descend over e

-- Identify under-saturated applications by introducing lambdas.

underIdentify :: Prog -> Prog
underIdentify p = onExp under p
  where
    env = [(f, length args) | Func f args e <- p ]

    under (App (Fun f) es) =
      case lookup f env of
        Nothing -> App (Fun f) es'
        Just n  -> if   length es < n
                   then Lam vs (App (Fun f) (es' ++ map Var vs))
                   else App (Fun f) es'
      where
        es' = map under es
        vs  = ['v' : show i | i <- [0..]] \\ (f:concatMap freeVars es')
    under e = descend under e


-- Eliminate lambdas.

-- A closure has a name, a list of closed variables, a list of
-- lambda variables and an unevaluated expression.

type Closure = (Id, [Id], [Id], Exp)

lamElim :: Prog -> (Prog, [Closure])
lamElim p = (p', cs)
  where
    (_, cs, p') = runWS (onExpM lam p) 0

    lam :: Exp -> WriterState Closure Int Exp
    lam (Lam vs e) =
      do e' <- lam e
         i <- get
         set (i+1)
         let c = "LAM_" ++ show i
         let ws = freeVars e'
         write (c, ws, vs, e')
         return (App (Con c) (map Var ws))
    lam e = descendM lam e

-- Construct the global closure-apply function.

constructApply :: [Closure] -> [Decl]

