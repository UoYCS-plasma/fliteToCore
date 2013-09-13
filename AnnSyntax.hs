module AnnSyntax where

import Syntax
import Data.List
import qualified Data.Map as Map
import Strictness

type VProg = [VDecl]

data VDecl = VDecl { declId :: Id
                   , declArgs :: [VPat]
                   , declBody  :: VExp } deriving Eq

data Van = Van { alg :: Bool, val :: Bool, strict :: Bool } deriving (Eq,Show)

-- annotated expression scheme as in Peyton Jones & Lester

type AExp a  = (a, AExp' a)

data AExp' a = AApp (AExp a) [AExp a]
             | ACase (AExp a) [AAlt a]
             | ALet (ABinding a) (AExp a)
             | AVar Id
             | ACon Id
             | AFun Id
             | AInt Int
             | AWld
             deriving (Eq,Show)

type VExp  = AExp Van
type VExp' = AExp' Van

isAlg :: VExp -> Bool
isAlg (a, e) = alg a

isVal :: VExp -> Bool
isVal (a, e) = val a

isStrict :: VExp -> Bool
isStrict (a, e) = strict a

mkAlg :: VExp -> VExp
mkAlg (van, e) = (van {alg=True}, e)

mkVal :: VExp -> VExp
mkVal (van, e) = (van {val=True}, e)

mkStrict :: VExp -> VExp
mkStrict (van, e) = (van {strict=True}, e)

type APat a = AExp a
type VPat   = APat Van

type AAlt a = (APat a, AExp a)
type VAlt   = AAlt Van

altLhs :: AAlt a -> APat a
altLhs = fst

altRhs :: AAlt a -> AExp a
altRhs = snd

type ABinding a = (APat a, AExp a)
type VBinding   = ABinding Van

idOf :: VExp -> Id
idOf (_,AVar id) = id
idOf (_,AFun id) = id
idOf (_,ACon id) = id
idOf e           = error ("idOf applied to " ++ show e)

callId :: VExp -> Id
callId (_,AApp f args) = idOf f

callArgs :: VExp -> [VExp]
callArgs (_,AApp f args) = args


defnOf :: VProg -> Id -> VDecl
defnOf ds id    = case find (\(VDecl id' _ _) -> id == id') ds of
                  Just d  -> d
                  Nothing -> error "defnOf applied to undeclared function id"

nullVan :: Van
nullVan = Van False False False

vanProg :: Strictness -> Prog -> VProg
vanProg str = map vanDecl
  where

  info  = Map.fromList str

  vanDecl (Func name args rhs) =
    VDecl name
          [ if b then mkVal (mkStrict e) else e
          | (e, b) <- zip (map vanExp args) bs]
          (vanExp rhs)
    where bs = info Map.! name

  vanExp :: Exp -> VExp
  vanExp e = (nullVan, vanExp' e)

  vanExp' :: Exp -> VExp'
  vanExp' (App fun args) = AApp (vanExp fun) (map vanExp args)
  vanExp' (Case e alts)  = ACase (vanExp e) (map vanAlt alts)
  vanExp' (Let bs e)     = case bs of
                           [b]   -> ALet (vanBinding b) (vanExp e)
                           other -> error "multiple bindings in let"
  vanExp' (Var v)        = AVar v
  vanExp' (Con c)        = ACon c
  vanExp' (Fun f)        = AFun f
  vanExp' (Int n)        = AInt n

  vanAlt :: Alt -> VAlt
  vanAlt (p, e)          = (vanExp p, vanExp e)

  vanBinding :: Binding -> VBinding
  vanBinding (id, e)     = (vanExp (Var id), vanExp e)

unVanProg :: VProg -> Prog
unVanProg = map unVanDecl

unVanDecl :: VDecl -> Decl
unVanDecl (VDecl name args body) = Func name (map unVanExp args) (unVanExp body)

unVanExp :: VExp -> Exp
unVanExp (van, e) = annotate van (unVanExp' e)

unVanExp' :: VExp' -> Exp
unVanExp' (AApp fun es)    = App (unVanExp fun) (map unVanExp es)
unVanExp' (ACase e alts)   = Case (unVanExp e) (map unVanAlt alts)
unVanExp' (ALet (v,e1) e2) = Let [(idOf v, unVanExp e1)] (unVanExp e2) 
unVanExp' (AVar id)        = Var id
unVanExp' (ACon id)        = Con id
unVanExp' (AFun id)        = Fun id
unVanExp' (AInt n)         = Int n 

unVanAlt :: VAlt -> Alt
unVanAlt (p, e) = (unVanExp p, unVanExp e)

annotate :: Van -> Exp -> Exp
annotate van e =
  case e of
  Fun id -> Fun (decorated id)
  Var id -> Var (decorated id)
  Con id -> Con (decorated id)
  other  -> if alg van || val van then App (Fun (decorated "")) [e]
            else e
  where
  decorated id = ['$' | val van] ++ ['@' | alg van] ++ id

prsProg :: Strictness -> VProg -> Prog
prsProg str = concatMap prsDecl
  where

  info  = Map.fromList str

  prsDecl :: VDecl -> [Decl]
  prsDecl (VDecl name args body) =
    [ Func (annId name args)
           (map prsExp args)
           (prsExp body) ] ++
    [ Func (annId (name ++ "!") args)
           (map prsExp args)
           (rhs (map prsExp args) (info Map.! name) (annId name args))
      | not (null args)
    ]

  rhs xs str f = foldr Force (App (Fun f) xs) strictIn
    where
      strictIn = [x | (Var x, True) <- zip xs str]

  prsExp :: VExp -> Exp
  prsExp (_, e) = prsExp' e

  prsExp' :: VExp' -> Exp
  prsExp' (AApp fun args)  = case fun of
                             (_,ACon cid) ->
                               App fun' args'
                             (_,AFun fid) ->
                               if isPrimId fid then
                                 if all isVal args then PRSApp fid args'
                                 else App (Fun fid) args'
                               else
                                 --App (Fun (annId fid args)) args'
                                 if and [ s <= isVal arg
                                        | (arg, s) <- zip args
                                                          (info Map.! fid)]
                                 then App (Fun (annId fid args)) args'
                                 else App (Fun (annId (fid++"!") 
                                        [ if s then mkVal arg else arg
                                        | (arg, s) <- zip args (info Map.! fid)])) args'
                             where
                             fun'  = prsExp fun
                             args' = map prsExp args            
  prsExp' (ACase e alts)   = Case (prsExp e) (map prsAlt alts)
  prsExp' (ALet (v,e1) e2) = Let [(idOf v, prsExp e1)] (prsExp e2) 
  prsExp' (AVar id)        = Var id
  prsExp' (ACon id)        = Con id
  prsExp' (AFun id)        = Fun id
  prsExp' (AInt n)         = Int n 

  prsAlt :: VAlt -> Alt
  prsAlt (p, e) = (prsExp p, prsExp e)

annId :: Id -> [VExp] -> Id
annId id es = id ++ map valChar es
  where
  valChar e = if isVal e then '$' else '?'
