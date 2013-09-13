module Case (completeCase, ctrFamilies) where

import Syntax
import Traversals
import Descend
import Control.Monad
import Data.List as List
import Data.Set as Set
import Data.Map as Map

-- Assumes that pattern matching has been desugared.

type Family = Set (Id, Int)

families :: Prog -> [Family]
families p
  | check = fams
  | otherwise = error "A constructor cannot have different arities!"
  where
    check = let ids = [id | (id, _) <- Set.toList (Set.unions fams)]
            in  length ids == length (nub ids)

    fams = fixMerge (List.map Set.fromList ctrs)

    merge [] = []
    merge (f:fs) = Set.unions (f:same) : merge different
      where (same, different) = List.partition (overlap f) fs

    fixMerge fs = if length fs == length fs' then fs' else fixMerge fs'
      where fs' = merge fs

    overlap f0 f1 = not (Set.null (Set.intersection f0 f1))

    ctrs = fromExp fam p

    fam e = [("True", 0), ("False", 0)]
          : List.map (concatMap getCtr) (caseAlts e)

    getCtr (App (Con c) ps, e) = [(c, length ps)]
    getCtr (Con c, e) = [(c, 0)]
    getCtr (p, e) = []

familyTable :: [Family] -> Map Id Family
familyTable fams =
  Map.fromList [(id, fam) | fam <- fams, (id, arity) <- Set.toList fam]

ctrFamilies :: Prog -> [[Id]]
ctrFamilies p =
  [List.map fst (Set.toList s) | s <- families p]

completeCase :: Prog -> Prog
completeCase p = expandCase (familyTable $ families p) p

expandCase :: Map Id Family -> Prog -> Prog
expandCase table p = onExp expand p
  where
    expand (Case e ((Var v, rhs):as)) = expand (Let [(v, e)] rhs)
    expand (Case e alts@((App (Con c) ps, rhs):as)) = Case (expand e) alts'
      where alts' = [getAlt f n | (f, n) <- Set.toAscList (table Map.! c)]
            getAlt f n = head ([ (App (Con c) args, expand rhs)
                               | (App (Con c) args, rhs) <- alts
                               , c == f ] ++ [bottom f n])
            bottom f n = (App (Con f) (replicate n (Var "_")), Bottom)
    expand e = descend expand e
