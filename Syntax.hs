module Syntax where

type Prog = [Decl]

data Decl = Func { funcName :: Id
                 , funcArgs :: [Pat]
                 , funcRhs  :: Exp }
  deriving Show

type Id = String

data Exp = App Exp [Exp]
         | Case Exp [Alt]
         | Let [Binding] Exp
         | Lam [Id] Exp
         | Var Id
         | Con Id
         | Fun Id
         | Int Int
         | Bottom
         | PRSApp Id [Exp]
         | Force Id Exp
  deriving (Eq, Show)

type Pat = Exp

type Alt = (Pat, Exp)

type Binding = (Id, Exp)

type App = [Exp]

-- Primitive functions

primIds = ["(+)", "(-)", "(==)", "(/=)", "(<=)"]

isPrimId :: Id -> Bool
isPrimId p = p `elem` primIds
