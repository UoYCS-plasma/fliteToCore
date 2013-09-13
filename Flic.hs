module Flic where

import Syntax
import Traversals
import Lift
import Match
import Case
import Let
import Identify
import Fresh
import Compile
import Pretty
import Inline
import Descend

flic :: Prog -> String
flic p = snd (runFresh (flicM p) "v_" 0)

flicM :: Prog -> Fresh String
flicM p =
  do p0 <- return (identifyFuncs p)
             >>= desugarEqn
             >>= desugarCase
             >>= onExpM freshen
             >>= inlineLinearLet
             >>= inlineSimpleLet
             >>= return . joinApps
             >>= return . spjCtrNotation
     return (prettyProg p0)

spjCtrNotation :: Prog -> Prog
spjCtrNotation p = onExp trCtr p
  where
    fs = ctrFamilies p
    m  = [(c, i) | fam <- fs, (c, i) <- zip fam [0..]]

    trCtr (Con c) = Con ("Pack{" ++ show (m!c) ++ ",0}")
    trCtr (App (Con c) es) =
      App (Con ("Pack{" ++ show (m!c) ++ "," ++ show (length es) ++ "}"))
          (map trCtr es)
    trCtr (Case e alts) =
      Case (trCtr e) [(trPat p, trCtr e) | (p, e) <- alts]
    trCtr other = descend trCtr other

    trPat (Con c) = Con ("<" ++ show (m!c) ++ ">")
    trPat other = descend trPat other
