module PRSAnalyse (prsAnalyse) where

import Data.List
import Data.Maybe
import Syntax
import Identify
import Dependency
import AnnSyntax
import ParseLib
import Parse
import Pretty
import Strictness
import System
import System.IO
import System.IO.Unsafe
import System.Console.GetOpt

type Context = [Int]

algProg :: VProg -> VProg
algProg = fixFrom (algProgC . algProgA)

fixFrom :: Eq a => (a->a) -> a -> a
fixFrom f x = firstDouble (iterate f x)
  where
  firstDouble (x:y:etc) = if x==y then x else firstDouble (y:etc)

-- Algebraic type oracle from Reduceron Memo 50
-- with mkAlg as the annotation function.
-- First the ana-pass: upward and outward propagation.

algProgA :: VProg -> VProg
algProgA ds                 = map algDeclA ds

algDeclA (VDecl f vs e)     = VDecl f vs' e'
                              where
                              vs' = map (liftAlg e') vs
                              e'  = algExpA e

algExpA n@(_, AInt _)       = n
algExpA v@(_, AVar _)       = v
algExpA c@(_, ACon _)       = c
algExpA (a, AApp fun es)    = (a, AApp fun (map algExpA es))
algExpA (a, ACase e alts)   = if any isAlg (map altRhs alts') then mkAlg e'
                              else e'
                              where
                              alts' = map algAltA alts
                              e'    = (a, ACase (mkAlg (algExpA e)) alts')
algExpA (a, ALet (v,e1) e2) = if isAlg e2' then mkAlg e' else e'
                              where
                              e1' = algExpA e1
                              e2' = algExpA e2
                              v'  = if isAlg e1' then mkAlg v else liftAlg e2' v
                              e'  = (a, ALet (v',e1') e2')

algAltA ((a,AApp c vs), e)  = (mkAlg (a,AApp c vs'), e')
                              where
                              e'  = algExpA e
                              vs' = map (liftAlg e') vs
algAltA ((a,c), e)          = (mkAlg (a,c), e')
                              where
                              e'  = algExpA e

liftAlg :: VExp -> VExp -> VExp
liftAlg e v = if isAlg v then v
              else if anyAlg e (idOf v) then mkAlg v
              else v

anyAlg :: VExp -> Id -> Bool
anyAlg (a,AVar v') v = v==v' && alg a
anyAlg (a,e)       v = anyAlg' e v

anyAlg' :: VExp' -> Id -> Bool
anyAlg' (AInt _)            v = False
anyAlg' (ACon _)            v = False
anyAlg' (AApp _ args)       v = any (flip anyAlg v) args
anyAlg' (ACase e alts)      v = anyAlg e v || any (flip anyAlg v . altRhs) alts
anyAlg' (ALet (v',e1) e2)   v = anyAlg e1 v || anyAlg e2 v 

-- Now the cata-pass: downward and inward propagation.

-- TO DO: propagate Alg from cases and lets inwards.

algProgC :: VProg -> VProg
algProgC ds                    = map (algDeclC ds) ds

algDeclC :: VProg -> VDecl -> VDecl
algDeclC ds (VDecl f vs e)     = VDecl f vs (algExpC ds (map idOf avs) e)
                                 where
                                 avs = filter isAlg vs

algExpC :: VProg -> [Id] -> VExp -> VExp
algExpC ds as n@(_,AInt _)         = n
algExpC ds as v@(_,AVar id)        = if id `elem` as then mkAlg v else v
algExpC ds as c@(_,ACon id)        = mkAlg c
algExpC ds as (a,AApp fun es)      = case fun of
                                     (_,ACon cid) ->
                                       mkAlg e'
                                     (_,AFun fid) ->
                                       if isPrimId fid then e'
                                       else passAlg body e''
                                       where
                                       VDecl name args body = defnOf ds fid
                                       e'' = (a, AApp fun (( map (algExpC ds as)
                                                          . zipWith passAlg args) es))
                                     other ->
                                       error ("application of "++show fun)
                                     where
                                     e' = (a, AApp fun (map (algExpC ds as) es))
algExpC ds as e@(a,ACase e1 alts)   = (a, ACase (mkAlg (algExpC ds as e1)) alts')
                                     where
                                     alts' = map (algAltC ds as e) alts
algExpC ds as e@(a,ALet (v,e1) e2) = (a, ALet (v,algExpC ds as' e1)
                                              (algExpC ds as' (passAlg e e2)) )
                                     where
                                     as' = as `union` (map idOf (filter isAlg [v]))

algAltC :: VProg -> [Id] -> VExp -> VAlt -> VAlt
algAltC ds as e0 ((a,AApp c vs), e1) = ( (a,AApp c vs)
                                       , algExpC ds as' (passAlg e0 e1) )
                                       where
                                       as' = as `union` (map idOf (filter isAlg vs))
algAltC ds as e0 ((a,ACon c), e1)    = ( (a,ACon c)
                                       , algExpC ds as (passAlg e0 e1) )

passAlg :: VExp -> VExp -> VExp
passAlg e1 e2 = if isAlg e1 then mkAlg e2 else e2

-- Analysis and improvement of valuable expressions
-- as in Memo 50.

-- The F pass.

valProgF :: Pool -> Pool
valProgF (Pool wds fds)     = Pool (map valDeclF wds) fds

valDeclF :: VDecl -> VDecl
valDeclF (VDecl f vs e)     = VDecl f vs (valExpF (map idOf vvs) e)
                              where
                              vvs = filter isVal vs

valExpF :: [Id] -> VExp -> VExp
valExpF vids n@(_,AInt _)       = n
valExpF vids v@(_,AVar id)      = if id `elem` vids then mkVal v else v
valExpF vids c@(_,ACon id)      = c
valExpF vids (a,AApp fun es)    = (a, AApp fun (map (valExpF vids) es))
valExpF vids (a,ACase e alts)   = (a, ACase (valExpF vids e) alts')
                                  where
                                  alts' = map (valAltF vids) alts
valExpF vids (a,ALet (v,e1) e2) = (a, ALet (v,valExpF vids e1) (valExpF vids' e2))
                                  where
                                  vids' = vids `union` (map idOf (filter isVal [v]))

valAltF :: [Id] -> VAlt -> VAlt
valAltF vids ((a,AApp c vs), e) = ((a,AApp c vs), valExpF vids' e)
                                   where
                                   vids' = vids `union` (map idOf (filter isVal vs))
valAltF vids ((a,ACon c), e)    = ((a,ACon c), valExpF vids e)

-- The B pass.

valProgB :: Pool -> (Pool, [VExp])
valProgB (Pool wds fds)     = ( Pool wds' fds, rqs )
                              where
                              (wds', rqss) = unzip (map (valDeclB (wds++fds)) wds)
                              rqs          = foldr reqMerge [] rqss

valDeclB :: VProg -> VDecl -> (VDecl, [VExp])
valDeclB ds (VDecl f vs e)  = ( VDecl f vs e' , rqs )
                              where
                              (e', rqs)   = valExpB ds e

valExpB ds n@(_, AInt _)       = ( mkVal n , [])
valExpB ds v@(_, AVar _)       = ( v , [] )
valExpB ds c@(_, ACon _)       = ( mkVal c , [])
valExpB ds (a, AApp fun es)    = case fun of
                                 (_,ACon cid) ->
                                   ( if all isVal es' then mkVal e' else e' , rqs )
                                 (_,AFun fid) ->
                                   if isPrimId fid then
                                     ( if all isVal es' then mkVal e' else e' , rqs )
                                   else
                                     case maybeDefnOf ds fid es' of
                                     Nothing ->
                                       (e', e':rqs)
                                     Just (VDecl _ args body) ->
                                       if isAlg body && isVal body then (mkVal e', rqs)
                                       else (e', rqs)
                                 other ->
                                   error ("application of "++show fun)
                                 where
                                 e'         = (a, AApp fun es')
                                 (es',rqss) = unzip (map (valExpB ds) es)
                                 rqs        = foldr reqMerge [] rqss
valExpB ds (a, ACase e1 alts)  = ( if alg a && all isVal (map altRhs alts') then mkVal e'
                                   else e'
                                 , rqs )
                                 where
                                 (e1',rqs1)   = valExpB ds e1
                                 (alts',rqss) = unzip (map (valAltB ds (isVal e1')) alts)
                                 e'           = (a, ACase e1' alts')
                                 rqs          = foldr reqMerge rqs1 rqss
valExpB ds (a, ALet (v,e1) e2) = ( passVal e2' e'
                                 , reqMerge rqs1 rqs2 )
                                 where
                                 (e1',rqs1) = valExpB ds e1
                                 (e2',rqs2) = valExpB ds e2
                                 v'         = passVal e1' v
                                 e'         = (a, ALet (v',e1') e2')

valAltB ds q ((a,AApp c vs), e)  = ( ((a,AApp c vs'), e') , rqs )
                                    where
                                    vs'       = if q then map mkVal vs else vs
                                    (e',rqs)  = valExpB ds e
valAltB ds q ((a,c), e)          = ( ((a,c), e') , rqs )
                                    where
                                    (e',rqs)  = valExpB ds e

passVal :: VExp -> VExp -> VExp
passVal e1 e2 = if isVal e1 then mkVal e2 else e2

reqMerge :: [VExp] -> [VExp] -> [VExp]
reqMerge = unionBy equivReq
  where
  equivReq (_,AApp f es) (_,AApp f' es') =
    idOf f == idOf f' &&
    and (zipWith equivVal es es')

equivVal :: VExp -> VExp -> Bool
equivVal e e' = isVal e == isVal e'

data Pool = Pool [VDecl] [VDecl]
            deriving Eq

allPoolDefns :: Pool -> [VDecl]
allPoolDefns (Pool wds fds) = wds ++ fds

maybeDefnOf :: [VDecl] -> Id -> [VExp] -> Maybe VDecl
maybeDefnOf ds id es = find matching ds
  where
  matching (VDecl id' vs _) = id' == id && and (zipWith matchVal vs es)

matchVal :: VExp -> VExp -> Bool
matchVal param arg =
  if isStrict param then True else isVal param == isVal arg

-- The D pass.

passD :: Context -> VProg -> Pool -> Pool
passD cxt prog (Pool wds fds) =
  -- unsafePerformIO (reportDecls "passD pool argument" wds)
  -- `seq`
  passD' cxt prog fds (strongComponentList wds)

passD' :: Context -> VProg -> [VDecl] -> [[VDecl]] -> Pool
passD' cxt prog fds []       = Pool [] fds
passD' cxt prog fds (ds:dss) =
  if length ds == 1 && nonRecursiveDecl (head ds) || all valIfAlgDecl ds then
    next
  else if dsR /= ds && all valIfAlgDecl dsRval then
    valuable (1:cxt) prog (formPool (concat dss) fds')
  else
    next
  where
  next         = passD' (2:cxt) prog (ds ++ fds) dss
  Pool [] fds' = valuable (0:cxt) prog (Pool dsR fds)
  dsR          = mkRecValIfAlg ds
  dsRval       = [d | VDecl fid args _ <- ds,
                 let Just d = maybeDefnOf fds' fid args]

strongComponentList :: [VDecl] -> [[VDecl]]
strongComponentList ds =
  map (map (annIdDecl ds)) (components (map callDeps ds))
  where
  callDeps d         = ( annId (declId d) (declArgs d)
                       , map callAnnId (funCallsInDecl d) )
  callAnnId e        = annId (callId e) (callArgs e)
  annIdDecl ds annId = let (id,annChars) = span (`notElem` "$?") annId
                       in fromJust (maybeDefnOf ds id (map charToAnnVar annChars))
  charToAnnVar '?'   = (nullVan, AWld)
  charToAnnVar '$'   = mkVal (nullVan, AWld)

valIfAlgDecl :: VDecl -> Bool
valIfAlgDecl (VDecl _ _ body) = if isAlg body then isVal body else True

-- Val-annotate every Alg-annotated application of a function
-- in the same component
mkRecValIfAlg :: [VDecl] -> [VDecl]
mkRecValIfAlg ds = map (rvaDecl ds) ds

rvaDecl :: [VDecl] -> VDecl -> VDecl
rvaDecl ds (VDecl f vs e)    = VDecl f vs (rvaExp ds e)

rvaExp :: [VDecl] -> VExp -> VExp
rvaExp ds n@(_,AInt _)       = n
rvaExp ds v@(_,AVar id)      = v
rvaExp ds c@(_,ACon id)      = c
rvaExp ds e@(a,AApp fun es)  = case fun of
                               (_,ACon cid) ->
                                 e'
                               (_,AFun fid) ->
                                 if isPrimId fid then e'
                                 else if isAlg e &&
                                         isJust (maybeDefnOf ds fid es) then mkVal e'
                                 else e'
                               where
                               e' = (a, AApp fun (map (rvaExp ds) es))
rvaExp ds (a,ACase e alts)   = (a, ACase (rvaExp ds e) (map (rvaAlt ds) alts))
rvaExp ds (a,ALet (v,e1) e2) = (a, ALet (v,rvaExp ds e1) (rvaExp ds e2))

rvaAlt :: VProg -> VAlt -> VAlt
rvaAlt ds (p, e) = (p, rvaExp ds e)

nonRecursiveDecl :: VDecl -> Bool
nonRecursiveDecl d = all nonRec (funCallsInDecl d)
  where
  nonRec (_, AApp fun args) = isNothing (maybeDefnOf [d] (idOf fun) args)

funCallsInDecl :: VDecl -> [VExp]
funCallsInDecl d = snd (valDeclB [] d)

formPool :: [VDecl] -> [VDecl] -> Pool
formPool wds fds = Pool (filter notAlreadyFinal wds) fds
  where
  notAlreadyFinal (VDecl fid args _) = isNothing (maybeDefnOf fds fid args)

-- overRideDecls :: Pool -> Pool -> Pool
-- overRideDecls (Pool wds fds) (Pool wds' fds') = Pool (wds' ++ filter notRedefined wds) [] -- ??
--   where
--   notRedefined (VDecl fid args _) = isNothing (maybeDefnOf wds' fid args)

-- collect f es ds collects just those declarations in ds
-- on which an application f es may depend
collect :: Id -> [VExp] -> Pool -> VProg
collect id0 args0 (Pool wds fds) = collect' [] [(nullVan,AApp (nullVan,AFun id0) args0)]
  where
  collect' p [] = p
  collect' p ((_,AApp (_,AFun id) args):es) =
    if isJust (maybeDefnOf p id args) then collect' p es
    else collect' (d : p) (funCallsInDecl d ++ es)
    where
    d = fromJust (maybeDefnOf (wds++fds) id args)

--prsAnalyse :: Prog -> Prog
--prsAnalyse = prsProg . prsAnalyseV . vanProg

prsAnalyse :: Strictness -> Prog -> Prog
prsAnalyse str = prsProg str . prsAnalyseV . vanProg str

prsAnalyseV :: VProg -> VProg
prsAnalyseV prog = collect f vs' (valuable [] prog' (Pool [VDecl f vs' e] []))
  where
  VDecl f vs e = head prog'
  vs'          = map mkVal vs
  prog'        = algProg prog

valuable :: Context -> VProg -> Pool -> Pool
valuable cxt prog pool =
  -- unsafePerformIO (putStrLn (customShow cxt))
  -- `seq`
  -- unsafePerformIO (reportDecls "valuable pool argument" pool)
  -- `seq`
  passD cxt prog pool'
  where
  ( pool' , [] ) = fixFrom (forwardAndBack prog) ( pool , [] )

-- auxiliary for tracing only
customShow :: Context -> String
customShow []      = ""
customShow (0:cxt) = '0':customShow cxt
customShow (1:cxt) = '1':customShow cxt
customShow cxt     = let (twos,cxt') = span (==2) cxt
                     in "<"++show (length twos)++">"++customShow cxt'

-- auxiliary for tracing only 
reportDecls :: String -> [VDecl] -> IO ()
reportDecls s p = do
  putStrLn (s++ " has "++show (length p)++" decls.")
  mapM_ (\d -> putStrLn (annId (declId d) (declArgs d))) p 

forwardAndBack :: VProg -> (Pool,[VExp]) -> (Pool,[VExp])
forwardAndBack prog (Pool wdefs fdefs,reqs) = 
  valProgB (valProgF pool')
  where
  defs  = map (variant prog) reqs
  pool' = Pool (defs ++ wdefs) fdefs

variant :: VProg -> VExp -> VDecl
variant prog (_,AApp f es) =
  VDecl fid args' body
  where
  VDecl fid args body = defnOf prog (idOf f)
  args'               = zipWith passValArg es args

passValArg :: VExp -> VExp -> VExp
passValArg e1 e2 = if isStrict e2 then mkStrict e3 else e3
  where e3 = if isVal e1 then mkVal e2 else e2


