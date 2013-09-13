module Lift (lambdaLift, caseAndLambdaLift) where

import Syntax
import Traversals
import Descend
import WriterState
import Control.Monad

type Lift a = WriterState Decl Int a

-- Lambda Lifter. Lifts lambdas to functions named "f___N" where is is a
-- natural number.  Therefore assumes function identifiers do not
-- already contain '___' character.

lambdaLift :: Prog -> Prog
lambdaLift = concatMap lamLiftDecl

lamLiftDecl :: Decl -> [Decl]
lamLiftDecl (Func f args rhs) = Func f args rhs' : ds
  where
    (_, ds, rhs') = runWS (lift f rhs) 0

    lift :: Id -> Exp -> Lift Exp
    lift f (Lam vs e) =
      do let ws = freeVarsExcept vs e
         i <- get
         set (i+1)
         let f' = f ++ "___" ++ show i
         e' <- lift f e
         write (Func f' (map Var (ws ++ vs)) e')
         return (app (Fun f') (map Var ws))
    lift f e = descendM (lift f) e

-- Case and lambda lifter.  As well as lambda lifting, lift each case
-- expression that does not occur at a spine position into new
-- function definition.

caseAndLambdaLift :: Prog -> Prog
caseAndLambdaLift = lambdaLift . onExp (mark True)
  where
    mark s (Case e alts)
      | s         = Case (mark True e) (markSnds True alts)
                    -- Modified (subject was marked as False)
      | otherwise = Lam [] (Case (mark False e) (markSnds True alts))
    mark s (Let bs e) = Let (markSnds False bs) (mark False e)
    mark s (App e es) = app (mark False e) (map (mark False) es)
    mark s (Lam vs e) = Lam vs (mark True e)
    mark s e = e

    markSnds :: Bool -> [(a, Exp)] -> [(a, Exp)]
    markSnds s ps = [(x, mark s y) | (x, y) <- ps]
