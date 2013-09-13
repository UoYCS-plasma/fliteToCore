import Syntax
import Parse
import Pretty
import Flic
import System.Environment

main :: IO ()
main =
  do [file] <- getArgs
     p <- parseProgFile file
     putStrLn (flic p)
