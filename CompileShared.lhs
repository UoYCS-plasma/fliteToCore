> module Compile where

> import List
> import Char
> import Syntax
> import Fresh
> import Flatten
> import Monad
> import Case

Target language
---------------

The target language is GNU C.  We represent C programs as strings.

> type C = String

Compilation monad
-----------------

I don't like it, but here we have a monad providing fresh names and a
writer capability for emitting code.

> data Compile a = Compile { runCompile :: Fresh (C, a) }

> instance Monad Compile where
>   return a = Compile $ return ("", a)
>   m >>= f = Compile $ do (c1, a) <- runCompile m
>                          (c2, b) <- runCompile (f a)
>                          return (c1 ++ c2, b)

> emit :: String -> Compile ()
> emit s = Compile $ return (s ++ "\n", ())

> block :: [String] -> Compile ()
> block [] = return ()
> block ss = mapM_ emit ss

> liftFresh :: Fresh a -> Compile a
> liftFresh m = Compile $ do { a <- m ; return ("", a) }

Atoms
-----

An atom is a machine word with a tag being stored in the bottom (least
significant) bits.  Atoms have capacity to store both tag and a
pointer.  For example, on a 32-bit machine, all words are alinged on
4-byte boundaries so the bottom 2 bits are free and a 2-bit tag is
stored there.

+-----+----------+--------------------+
| Tag | Acronym  |  Meaning           |
+-----+----------+--------------------+
| 00  |   PTR    |  Heap address      |
| 01  |   CTR    |  Constructor       |
| 10  |   INT    |  Integer           |
| 11  |   FUN    |  Function address  |
+-----+----------+--------------------+

> atomDecls :: Compile ()
> atomDecls =
>   block [
>     "typedef unsigned long Atom;"
>   , "#define isPTR(a)   (((a)&3) == 0)"
>   , "#define isCTR(a)   (((a)&3) == 1)"
>   , "#define isINT(a)   (((a)&3) == 2)"
>   , "#define isFUN(a)   (((a)&3) == 3)"
>   , "#define getPTR(a)  ((Atom*) (a))"
>   , "#define getCTR(a)  ((a) >> 2)"
>   , "#define getINT(a)  ((long) (((long) (a)) >> 2))"
>   , "#define getFUN(a)  ((void*) (((unsigned long) (a)) & (~3)))"
>   , "#define makePTR(x) ((Atom) (x))"
>   , "#define makeCTR(x) ((Atom) (((x) << 2) | 1))"
>   , "#define makeINT(x) ((Atom) ((((unsigned long) (x)) << 2) | 2))"
>   , "#define makeFUN(x) ((Atom) (((unsigned long) (x)) | 3))"
>   ]

Stacks
------

There are two stacks: R-Stack and L-Stack.

The top of the R-Stack stores a pointer to the application currently
under evaluation and a return address to jump to when evaluation is
complete.  The R-Stack grows backwards in memory.

> rStackFrame :: Compile ()
> rStackFrame =
>   block [
>     "typedef struct {"
>   , "  Atom* current;"
>   , "  void* returnAddress;"
>   , "} Frame;"
>   ]

The L-stack contains the local variables of functions.  In particular,
it stores arguments, pointers to applications that have been built on
the heap, and results of case-subject and primitive-argument
evaluations.  The L-Stack grows forwards in memory.

> lStackCode :: Compile ()
> lStackCode =
>   block
>     [ "#define L_POP(n) L_sp-=n; L_top = L_sp[-1];"
>     , "#define L_PUSH(a) L_top = a; L_sp[0] = L_top; L_sp++;"
>     ]

> rStackCode :: Compile ()
> rStackCode =
>   block
>     [ "#define R_POP \\"
>     , "  R_sp++;\\"
>     , "  R_top_returnAddress = R_sp[1].returnAddress;\\"
>     , "  R_top_current = R_sp[1].current;"
>     , "#define R_PUSH(ra, cur) \\"
>     , "  R_top_returnAddress = R_sp[0].returnAddress = ra; \\"
>     , "  R_top_current = R_sp[0].current = cur; \\"
>     , "  R_sp--;"
>     ]

Global variables
----------------

> globals :: Compile ()
> globals =
>   block
>     [ "#define HEAP_SIZE 10000000"
>     , "#define STACK_SIZE 1000000"
>     , "register Atom* L_sp;"  -- L-stack pointer
>     , "Atom* L_base;"
>     , "register Atom L_top;"
>     , "register Frame* R_sp;"  -- R-stack pointer
>     , "Frame* R_base;"
>     , "register void* R_top_returnAddress;"
>     , "register Atom* R_top_current;"
>     , "register Atom* hp;"     -- Heap pointer
>     , "register Atom* heapEnd;"
>     , "register Atom atom;"
>     , "register Atom* app;"
>     , "register long res;"
>     , "Atom* fromSpace;"
>     , "Atom* toSpace;"
>     , "Atom* fromSpaceEnd;"
>     , "Atom* toSpaceEnd;"
>     , "Atom* scan;"
>     , "Atom* free;"
>     , "Atom* p;"
>     , "Atom* from;"
>     , "Frame* frame;"
>     , "void* gc_copy_ret;"
>     , "void* gc_ret;"
>     , "void* eval_ret_addr;"
>     , "int i;"
>     , "int j;"
>     , "int n;"
>     , "int m;"
>     ]

Compiler
========

Invariants
----------

Invariant 1: case expressions are only allowed at spine positions.  An
expression is at a spine position if it is the root of a function body
or case alternative.  If a let is at a spine position then the body of
a let is also at a spine position.

Invariant 2: case expressions have non-nested patterns.

Invariant 3: programs are first-order.

Environment
-----------

Terms are compiled within an environment which maps variables to
stack or heap offsets.

> type Env = [(Id, Offset)]

> data Offset =
>    Stack Int
>  | StackArg Int Int
>  | Heap Int
>  | Val Int

> offset :: Offset -> String
> offset (Stack o)       =  "L_sp[-" ++ show o ++ "]"
> offset (StackArg o i)  =  "getPTR(L_sp[-" ++ show o ++ "])"
>                       ++  "[" ++ show i ++ "]"
> offset (Heap o)        =  "makePTR(hp+" ++ show o ++ ")"
> offset (Val o)         =  "hp[" ++ show o ++ "]"

> incStack :: Int -> Env -> Env
> incStack n  =  map f
>   where
>     f (v, StackArg i j)  =  (v, StackArg (i+n) j)
>     f (v, Stack i)       =  (v, Stack (i+n))
>     f other              =  other

Term Construction
-----------------

The "build" function constructs an expression on the heap and leaves a
pointer to the spine application in the C variable "atom".  The
expressions must not contain a case expression.  Assumes no name
shadowing.

> build :: Env -> Exp -> Compile ()
> build env (Var v) =
>   block [ "atom = " ++ offset (env!v) ++ ";" ]
> build env (Int i) =
>   block [ "atom = makeINT(" ++ show i ++ ");" ]
> build env (Con c) =
>   block [ "atom = makeCTR(" ++ conName c ++ ");" ]
> build env (Fun c) =
>   block [ "atom = makeFUN(" ++ funName c ++ ");" ]
> build env e =
>   do (bs, spine) <- liftFresh (flatten e)
>      let os = scanl (+) 0 [size e | (v, e) <- bs]
>      let env' = [ (v, case e of PRSApp _ _ -> Val o ; other -> Heap o)
>                 | ((v, e), o) <- zip bs os] ++ env
>      sequence_ [writeApp env' e o | ((v, e), o) <- zip bs os]
>      writeApp env' spine (last os)
>      block
>        [ "atom = makePTR(hp+" ++ show (last os) ++ ");"
>        , "hp += " ++ show (last os + size spine) ++ ";"
>        ]

Check heap and call garbage collector if necessary.

> heapCheck :: Compile ()
> heapCheck =
>   do n <- liftFresh freshInt
>      let label = "GC_RET_" ++ show n
>      block
>        [ "if (hp > heapEnd) {"
>        --, "printf(\"Stack: %i %i\\n\", L_sp - L_base, R_base - R_sp);"
>        , "  gc_ret = &&" ++ label ++ ";"
>        , "  goto GC_COLLECT;"
>        , "}"
>        , "  " ++ label ++ ":"
>        ]

Size of an application.

> size (Int i)       =  2
> size (Var v)       =  2
> size (App f xs)    =  2 + length xs
> size (PRSApp f xs) =  1
> size other         =  error "size: invalid argument"

Append an application onto the heap.

> writeApp :: Env -> Exp -> Int -> Compile ()
> writeApp env (PRSApp f [e1, e2]) o =
>   case arith f of
>     True  -> emit (lhs ++ "makeINT(" ++ prsEval env f e1 e2 ++ ");")
>     False -> emit (lhs ++ "makeCTR(" ++ prsEval env f e1 e2 ++ ");")
>   where lhs = "hp[" ++ show o ++ "] = "
> writeApp env e o =
>   do emit ("hp[" ++ show o ++ "] = makeHDR(" ++ show (size e - 1) ++ ");")
>      case e of
>         App f xs -> writeAtoms env (f:xs) (o+1)
>         other    -> writeAtoms env [e] (o+1)

> writeAtoms env [] o      =  return ()
> writeAtoms env (x:xs) o  =  writeAtom env x o >> writeAtoms env xs (o+1)

> writeAtom env (Int i) o  = 
>   emit ("hp[" ++ show o ++ "] = makeINT(" ++ show i ++ ");")
> writeAtom env (Var v) o  =  
>   emit ("hp[" ++ show o ++ "] = " ++ offset (env!v) ++ ";")
> writeAtom env (Con c) o  = 
>   emit ("hp[" ++ show o ++ "] = makeCTR(" ++ conName c ++ ");")
> writeAtom env (Fun f) o  = 
>   emit ("hp[" ++ show o ++ "] = makeFUN(&&" ++ funName f ++ ");")

In the generated code, function and constructor names will be
uniquely prefixed to avoid name clashes.

> funName :: Id -> String
> funName "(+)" = "P_ADD"
> funName "(-)" = "P_SUB"
> funName "(==)" = "P_EQ"
> funName "(/=)" = "P_NEQ"
> funName "(<=)" = "P_LEQ"
> funName n = "F_" ++ encode n

> encode "" = ""
> encode (c:cs)
>   | c == '$' = "_V_" ++ encode cs
>   | c == '@' = "_A_" ++ encode cs
>   | c == '?' = "_Q_" ++ encode cs
>   | otherwise = c : encode cs

> conName :: Id -> String
> conName n = "C_" ++ n

Evaluation
----------

The "evalApp" function generates C code that evaluates an application
(pointed-to by the C variable "app") to a normal form.  After
evaluation, the application is overwritten with the result and the
result is pushed onto the L-Stack.

> evalCode :: Compile ()
> evalCode = 
>   do block
>        [ "EVAL:"
>        , "if (isPTR(atom)) {"
>        , "  app = getPTR(atom);"
>        , "  EVAL_APP:"
>        , "  if (isFUN(app[1])) {"
>        , "    L_PUSH(makePTR(app));"
>        , "    R_PUSH(eval_ret_addr, app);"
>        , "    goto *getFUN(app[1]);"
>        , "    EVAL_RET:"
>        , "    if (R_top_current) {"
>        , "      R_top_current[0] = makeHDR(1);"
>        , "      R_top_current[1] = L_top;"
>        , "    }"
>        , "    eval_ret_addr = R_top_returnAddress;"
>        , "    R_POP;"
>        , "    goto *eval_ret_addr;"
>        , "  }"
>        , "  else if (isCTR(app[1])) {"
>        , "    L_PUSH(makePTR(app)); res = getCTR(app[1]);"
>        , "    goto *eval_ret_addr;"
>        , "  }"
>        , "  else if (isPTR(app[1])) {"
>        , "    app = getPTR(app[1]);"
>        , "    goto EVAL_APP;"
>        , "  }"
>        , "  else {"
>        , "    L_PUSH(app[1]); res = getINT(app[1]);"
>        , "    goto *eval_ret_addr;"
>        , "  }"
>        , "} else {"
>        , "  L_PUSH(atom);"
>        , "  res = getINT(atom);"
>        , "  goto *eval_ret_addr;"
>        , "}"
>        ]

> eval :: Compile ()
> eval =
>   do label <- liftFresh freshInt
>      block [ "eval_ret_addr = &&LABEL_" ++ show label ++ ";"
>            , "goto EVAL;"
>            , "LABEL_" ++ show label ++ ":"
>            ]

> tailEvalCode :: Compile ()
> tailEvalCode = 
>   do block
>        [ "TAIL_EVAL:"
>        , "if (isPTR(atom)) {"
>        , "  app = getPTR(atom);"
>        , "  TAIL_EVAL_APP:"
>        , "  if (isFUN(app[1])) {"
>        , "    L_PUSH(makePTR(app));"
>        , "    if (R_top_current) {"
>        , "      R_top_current[0] = makeHDR(1);"
>        , "      R_top_current[1] = makePTR(app);"
>        , "    }"
>        , "    R_top_current = R_sp[1].current = app;"
>        , "    goto *getFUN(app[1]);"
>        , "  }"
>        , "  else if (isPTR(app[1])) {"
>        , "    app = getPTR(app[1]);"
>        , "    goto TAIL_EVAL_APP;"
>        , "  }"
>        , "  else if (isINT(app[1])) {"
>        , "    L_PUSH(app[1]); res = getINT(app[1]);"
>        , "    goto EVAL_RET;"
>        , "  }"
>        , "  else {"
>        , "    L_PUSH(makePTR(app)); res = getCTR(app[1]);"
>        , "    goto EVAL_RET;"
>        , "  }"
>        , "} else {"
>        , "  L_PUSH(atom);"
>        , "  res = getINT(atom);"
>        , "  goto EVAL_RET;"
>        , "}"
>        ]

> tailEval :: Compile ()
> tailEval = emit "goto TAIL_EVAL;"

Compilation
-----------

Compile an expression.  Assumes case expressions only occur in spine
positions.  The integer argument contains the current size of the
stack frame for the function body being compiled.  The boolean
argument records whether the expression to compile is in a
tail-position or not.

> comp :: Env -> Int -> Bool -> Exp -> Compile ()
> comp env n tail (Int i) =
>   do lpop n
>      block
>        [ "L_PUSH(makeINT(" ++ show i ++ "));"
>        , "res = " ++ show i ++ ";"
>        ]
>      block [ "goto EVAL_RET;" | tail ]
> comp env n tail (Var v) =
>   do block [ "atom = " ++ offset (env!v) ++ ";" ]
>      lpop n
>      case tail of
>        False -> eval
>        True  ->
>          do tailEval 
>             emit "goto EVAL_RET;"
> comp env n tail (Con c) = 
>   do lpop n
>      block
>        [ "L_PUSH(makeCTR(" ++ conName c  ++ "));"
>        , "res = " ++ conName c ++ ";"
>        ]
>      block [ "goto EVAL_RET;" | tail ]
> -- MISSING CASE (Fun f)
> comp env n tail (App (Fun f) [x, y]) | isPrimId f =
>   do comp env 0 False x
>      comp (incStack 1 env) 0 False y
>      emit "L_POP(1);"
>      case f of
>        "(+)"  -> emit "res = getINT(L_top) + res;"
>               >> lpop (n+1)
>               >> emit "L_PUSH(makeINT(res));"
>        "(-)"  -> emit "res = getINT(L_top) - res;"
>               >> lpop (n+1)
>               >> emit "L_PUSH(makeINT(res));"
>        "(==)" -> emit "res = getINT(L_top) == res ? C_True : C_False;"
>               >> lpop (n+1)
>               >> emit "L_PUSH(makeCTR(res));"
>        "(/=)" -> emit "res = getINT(L_top) != res ? C_True : C_False;"
>               >> lpop (n+1)
>               >> emit "L_PUSH(makeCTR(res));"
>        "(<=)" -> emit "res = getINT(L_top) <= res ? C_True : C_False;"
>               >> lpop (n+1)
>               >> emit "L_PUSH(makeCTR(res));"
>      block [ "goto EVAL_RET;" | tail ]
> comp env n tail e | isApp e =
>   do let f = appCall e
>      build env e
>      lpop n
>      case f of
>        Con c -> block [ "L_PUSH(atom);"
>                       , "res = " ++ conName c ++ ";" ]
>              >> block [ "goto EVAL_RET;" | tail ]
>        Fun f -> case tail of
>                   False -> eval
>                   True  -> block [ "L_PUSH(atom);"
>                                  , "goto " ++ funName f ++ ";" ]
> comp env n tail (Case e alts) =
>   do comp env 0 False e
>      emit "switch (res) {"
>      mapM_ compileAlt alts
>      emit "}"
>   where
>     compileAlt (Con c, e) =
>       do emit ("case " ++ conName c ++ ":")
>          comp (incStack 1 env) (n+1) tail e
>          block ["break;" | not tail]
>     compileAlt (App (Con c) ps, e) =
>       do emit ("case " ++ conName c ++ ":")
>          let vs = map (\(Var v) -> v) ps
>          let env' = incStack 1 env
>          let env'' = zip vs [StackArg 1 i | i <- [2..]] ++ env'
>          comp env'' (n+1) tail e
>          block ["break;" | not tail]
> comp env n tail (PRSApp f [e1, e2]) =
>   do emit ("res = " ++ prsEval env f e1 e2 ++ ";")
>      lpop n
>      case arith f of
>        True  -> emit "L_PUSH(makeINT(res));"
>        False -> emit "L_PUSH(makeCTR(res));"
>      block ["goto EVAL_RET;" | tail]

> prsEval env f e1 e2
>   | arith f = val e1 ++ op f ++ val e2
>   | otherwise = val e1 ++ op f ++ val e2 ++ "? C_True : C_False"
>   where
>     val (Int i) = show i
>     val (Var v) = "getINT(" ++ offset (env!v) ++ ")"
>     op "(+)"    = "+"
>     op "(-)"    = "-"
>     op "(==)"   = "=="
>     op "(/=)"   = "!="
>     op "(<=)"   = "<="
     
> arith f = f `elem` ["(+)", "(-)"]

> isApp :: Exp -> Bool
> isApp (App (Fun f) xs) = not (isPrimId f)
> isApp (App (Con f) xs) = True
> isApp (Let bs t) = isApp t
> isApp other      = False

> appCall :: Exp -> Exp
> appCall (App f xs) = f
> appCall (Let bs t) = appCall t

> lpop :: Int -> Compile ()
> lpop 0 = return ()
> lpop n = block [ "L_POP(" ++ show n ++");" ]

Compile a function definition.

> compileDecl :: Decl -> Compile ()
> compileDecl (Func f [] e) | f /= "main" = error "0-arity funs not handled!"
> compileDecl (Func f ps e) =
>   emit (funName f ++ ":") >>  -- emit ("printf(\"" ++ f ++ "\\n\");") >> 
>     heapCheck >> comp env 1 True e
>   where
>     vs = map (\(Var v) -> v) ps
>     env = [(v, StackArg 1 i) | (v, i) <- zip vs [2..]]

> prims :: Compile ()
> prims =
>   do prim "(+)"
>      prim "(-)"
>      prim "(==)"
>      prim "(/=)"
>      prim "(<=)"

> prim :: String -> Compile ()
> prim p = compileDecl d
>  where
>    d = Func p [Var "x", Var "y"] (App (Fun p) [Var "x", Var "y"])

Compile a program to C.

> compile :: Prog -> Fresh C
> compile p = return fst `ap` runCompile compiler
>   where
>     compiler =
>       do emit "#include <stdio.h>"
>          emit "#include <stdlib.h>"
>          atomDecls
>          rStackFrame
>          lStackCode
>          rStackCode
>          visitedMacros
>          mapM defineFamily (ctrFamilies p)
>          emit "\n\nvoid main() {"
>          globals
>          initialise
>          start
>          evalCode
>          tailEvalCode
>          mapM compileDecl p
>          prims
>          copy
>          collect
>          emit "}"

> defineFamily :: [Id] -> Compile ()
> defineFamily cs = zipWithM_ defineCtr cs [0..]

> defineCtr c n = emit ("#define " ++ conName c ++ " " ++ show n)

> initialise =
>   block
>     [ "L_base = L_sp = malloc(sizeof(Atom) * STACK_SIZE);"
>     , "R_base = R_sp = (Frame*) &L_sp[STACK_SIZE-1];"
>     , "fromSpace = hp = malloc(sizeof(Atom) * HEAP_SIZE);"
>     , "heapEnd = fromSpaceEnd = &fromSpace[HEAP_SIZE-1000];"
>     , "toSpace = malloc(sizeof(Atom) * HEAP_SIZE);"
>     , "toSpaceEnd = &toSpace[HEAP_SIZE-1000];"
>     ]

> start = 
>   do emit "R_PUSH(&&MAIN_RET, 0); L_sp++;"
>      emit "goto F_main;"
>      emit "MAIN_RET:"
>      emit "printf(\"%i\\n\", getINT(L_top));"
>      --emit "printf(\"Stack sz: %i %i\\n\", L_sp - L_base, R_base - R_sp);"
>      emit "return;"

Garbage collection
------------------

THE LSB of the header cell of an allocated region is used as a
"visited" marker.

> visitedMacros = 
>   block
>     [ "#define makeHDR(x)        ((x) << 1)"
>     , "#define VISITED           1"
>     , "#define size(x)           ((x) >> 1)"
>     ]

> copy :: Compile ()
> copy =
>   block
>     [ "GC_COPY:"
>     , "if (from[0] == VISITED) {"
>     , "  atom = from[1];"
>     , "  goto *gc_copy_ret;"
>     , "}"
>     , "if (isPTR(from[1])) { from = getPTR(from[1]); goto GC_COPY; }"
>     , "if (size(from[0]) == 1) { atom = from[1]; }"
>     , "else {"
>     , "  n = size(from[0]) + 1;"
>     , "  //printf(\"Copy (%i);\\n\", n-1);"
>     , "  atom = makePTR(free);"
>     , "  for (i = 0; i < n; i++)"
>     , "    { *free = from[i]; free++; }"
>     , "  from[0] = VISITED;"
>     , "  from[1] = atom;"
>     , "}"
>     , "goto *gc_copy_ret;"
>     ]

> collect :: Compile ()
> collect =
>   block
>     [ "GC_COLLECT:"
>     , "//printf(\"GC invoked (%i);\\n\", hp - fromSpace);"
>     , "scan = toSpace;"
>     , "free = toSpace;"
>     , "for (p = L_base; p < L_sp; p++) {"
>     , "  if (isPTR(*p)) {"
>     , "    from = getPTR(*p);"
>     , "    gc_copy_ret = &&GC_COPY_RET1; goto GC_COPY; GC_COPY_RET1:"
>     , "    *p = atom;"
>     , "  }"
>     , "}"
>     --, "printf(\"GC scanning;\\n\");"
>     , "while (scan < free) {"
>     , "  m = size(*scan); scan++;"
>     , "  //printf(\"Scan (%i);\\n\", m);"
>     , "  for (j = 0; j < m; j++) {"
>     , "    if (isPTR(*scan)) {"
>     , "      from = getPTR(*scan);"
>     , "      gc_copy_ret = &&GC_COPY_RET2; goto GC_COPY; GC_COPY_RET2:"
>     , "      *scan = atom;"
>     , "    }"
>     , "    scan++;"
>     , "  }"
>     , "}"
>     --, "printf(\"Remapping R stack;\\n\");"
>     , "for (frame = R_base; frame > R_sp; frame--) {"
>     , "  p = frame->current;"
>     , "  frame->current = 0;"
>     , "  while (p && p[0] != VISITED && isPTR(p[1])) p = getPTR(p[1]);"
>     , "  if (p && p[0] == VISITED) {"
>     , "    if (isPTR(p[1])) frame->current = getPTR(p[1]);"
>     , "  }"
>     , "}"
>     , "hp = free;"
>     , "p = fromSpace; fromSpace = toSpace; toSpace = p;"
>     , "p = fromSpaceEnd; fromSpaceEnd = toSpaceEnd; toSpaceEnd = p;"
>     , "heapEnd = fromSpaceEnd;"
>     , "L_top = L_sp[-1];"
>     , "R_top_returnAddress = R_sp[1].returnAddress;"
>     , "R_top_current = R_sp[1].current;"
>     , "//printf(\"GC finished (%i);\\n\", hp - fromSpace);"
>     , "goto *gc_ret;"
>     ]

Auxiliary Functions
-------------------

> (!) :: (Eq a, Show a) => [(a, b)] -> a -> b
> m ! k =
>   case lookup k m of
>     Nothing -> error ("Key " ++ show k ++ " not in environment")
>     Just v  -> v
