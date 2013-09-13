module Pretty where

import Syntax
import PrettyLib

putProg :: Prog -> IO ()
putProg = putDoc . enclose line line . indent 2 . vsep . punctuate (semi <> line) . map pretty
  
prettyProg :: Prog -> String
prettyProg = show . enclose line line . indent 2 . vsep . punctuate (semi <> line) . map pretty
  
instance Pretty Decl where
    pretty (Func f a r) = nest 2 $ text f
              <+> hsep (map prettyArg a)
              </> char '='
              <+> pretty r
              
instance Pretty Exp where
    pretty (App (Fun f) [x,y])
      | isPrimId f = parens $ hsep [pretty x, unBracket f, pretty y]
    pretty (App x ys)   = hsep (prettyArg2 x : map prettyArg ys)
    pretty (PRSApp x ys) = 
      text "{" </> hsep (text x : map prettyArg ys) </> text "}"
    pretty (Case x as)  = nest 2 (text "case" </> pretty x)
              </> nest 2 (text "of" </> prettyBlock prettyAlt as)
    pretty (Let bs y)  = nest 2 (text "let" </> prettyBlock prettyBind bs)
              </> nest 2 (text "in" </> prettyArg y)
    pretty (Lam vs x)  = nest 2 (text "\\" <> (hsep . map text $ vs) </> text "->" </> pretty x)
    pretty (Var v)    = text v
    pretty (Fun f)    = text f
    pretty (Con c)    = text c
    pretty (Int i)    = int i
    pretty (Bottom)   = text "undefined"
    pretty (Force x e) = text x </> text "`seq`"  </> pretty e
  
unBracket s = text [x | x <- s, x /= '(', x /= ')']

prettyBlock :: (a -> Doc) -> [a] -> Doc
prettyBlock f = enclose line line . vsep . punctuate semi . map f
  
prettyAlt :: Alt -> Doc
prettyAlt (p, x) = nest 2 $ pretty p <+> text "->" </> pretty x
  
prettyBind :: Binding -> Doc
prettyBind (v, x) = text v <+> text "=" <+> pretty x
  
prettyArg :: Exp -> Doc
prettyArg (App e []) = prettyArg e
prettyArg e@(App _ _) = parens . pretty $ e
prettyArg e@(Case _ _) = parens . pretty $ e
prettyArg e@(Let _ _) = parens . pretty $ e
prettyArg e@(Lam _ _) = parens . pretty $ e
prettyArg e = pretty e
  
prettyArg2 :: Exp -> Doc
prettyArg2 (App e []) = prettyArg e
prettyArg2 e@(Case _ _) = parens . pretty $ e
prettyArg2 e@(Let _ _) = parens . pretty $ e
prettyArg2 e@(Lam _ _) = parens . pretty $ e
prettyArg2 e = pretty e
  
showPretty :: Pretty a => a -> String
showPretty = (++ "\n") . show  . indent 2 . pretty
  
-- instance Show Decl where
--  show = ('\n':) . show  . pretty
    
-- instance Show Exp where
--  show = ('\n':) . show . pretty
