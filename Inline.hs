module Inline (inline, caseCase, caseCon) where

import Syntax
import Traversals
import ConcatApp
import Descend
import Fresh
import Dependency
import Control.Monad
import Let
import Debug.Trace

-- In-line saturated applications of small, non-recursive functions
inline :: Prog -> Fresh Prog
inline p = onExpM inl p
  where
    cg = closure (callGraph p)
    inl (App (Fun f) es)
      | f `notElem` depends cg f =
        case lookupFuncs f p of
          Func f args rhs:_
            | linear [v | Var v <- args] rhs
           && numApps rhs <= 5 -> trace (show f) $
                do let vs = [v | Var v <- args]
                   rhs' <- freshen rhs
                   let rhs'' = substMany rhs' (zip es vs)
                   inl rhs''
          _ -> liftM (mkApp (Fun f)) (mapM inl es)
    
    inl e = descendM inl e

linear vs e = and [ varRefs v e <= 1 | v <- vs ]

mkApp f [] = f
mkApp f es = App f es

mkLet [] e = e
mkLet bs e = Let bs e

numApps (App f xs) = 1 + sum (map numApps (f:xs))
numApps (Let bs e) = sum (map numApps (e:map snd bs))
numApps (Case e as) = max 1 (numApps e) + sum (map (numApps . snd) as)
numApps e = 0;

-- Case of case transformation
caseCase :: Prog -> Prog
caseCase p = onExp cc p
  where
    pats alts = [p | (p, e) <- alts]
    exps alts = [e | (p, e) <- alts]
    cc (Case (Case e alts1) alts2) =
      cc $ Case e (zip (pats alts1) [Case r alts2 | r <- exps alts1])
    cc e = descend cc e

-- Case of known-construction simplification
caseCon :: Prog -> Prog
caseCon p = onExp cc p
  where
    vars xs = [v | Var v <- xs]
    cc (Case (Con c) alts) = cc (Case (App (Con c) []) alts)
    cc (Case (App (Con c) as) alts) =
      cc $ head $ [ Let (zip (vars bs) (as)) e
                  | (App (Con d) bs, e) <- alts, c == d]
               ++ [ e | (Con d, e)  <- alts, c == d]
    cc e = descend cc e
