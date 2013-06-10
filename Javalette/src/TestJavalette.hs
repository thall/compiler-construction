--------------------------------------------------------------------------------
-- Compiler Construction 
-- TDA282
-- Niclas Tall

module Main where

import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import System.IO 
import System.Process (waitForProcess, runCommand)
import System.FilePath.Posix(splitExtension, splitFileName, splitPath)
import System.Exit

import Data.Char

import AbsJavalette
import LexJavalette
import PrintJavalette
import ParJavalette
import ErrM

import TypeChecker
import CodeGeneration.JVM
import CodeGeneration.LLVM

printError :: String -> IO ()
printError s = hPutStrLn stderr s

parse :: String -> IO Program
parse s =
  case pProgram (myLexer s) of
    Bad err  -> do printError "PARSE ERROR"
                   putStrLn err
                   exitFailure 
    Ok  tree -> return tree

-- Returns a type annotated AST
typecheck :: Program -> IO Program
typecheck ast =
  case runTypeChecker ast of
    Bad err  -> do printError "ERROR"
                   putStrLn err
                   exitFailure 
    Ok tree' -> do printError "OK"
                   putStrLn $ show tree'
                   return tree'

-- Returns either JVM or LLVM assembler 
codeGen :: String -> Bool -> Program -> IO String
codeGen file jvm tast =
  if jvm then
    case genJVM file tast of
      (Left err, c) -> do printError $ "Error Msg: " ++ err
                          (putStrLn . unlines . (map show)) c
                          exitFailure
      (Right _, c)  -> do printError "OK"    
                          (return . unlines . (map show)) c
  else do (return . unlines . map show . genLLVM) tast
 
compileJasmin :: FilePath -> String -> IO ()
compileJasmin f c = do
  let f' = f ++ ".j"
  writeFile f' c 
  let dir = concat $ (\p -> take (length p - 1) p) $ splitPath f
  h <- runCommand $ "java -jar lib/jasmin.jar -d " ++ dir ++ " " ++ f'
  status <- waitForProcess h
  case status of 
    ExitSuccess      -> printError "Java binary created"
    (ExitFailure i)  -> printError $ "Failed to compile Jasmin assembler, err msg: " ++ show i

compileLLVM :: FilePath -> String -> IO ()
compileLLVM path code = do
  writeFile (path ++ ".ll") code
  ph <- runCommand $ "opt -std-compile-opts " ++ path ++ ".ll" ++ " > " ++ path ++ ".bc"
  status <- waitForProcess ph
  case status of
    ExitSuccess     -> printError "LLVM optimized bitcode file created" 
    (ExitFailure m) -> printError $ "Failed to create LLVM File, err msg: " ++ show m

compile :: String -> String -> IO ()
compile filePath s = do
  ast  <- parse s
  tast <- typecheck ast

  -- path/to/file
  let filePathWOExt = (fst . splitExtension) filePath
  -- Filename
  let fileName  = (snd. splitFileName) filePathWOExt
 
  jvmCode   <- codeGen fileName True  tast
  llvmCode  <- codeGen fileName False tast
  compileJasmin filePathWOExt jvmCode
  compileLLVM   filePathWOExt llvmCode

main :: IO ()
main = do args <- getArgs
          case args of
            [file] -> readFile file >>= compile file
            _      -> do putStrLn "./jlc <source>"
                         exitFailure
