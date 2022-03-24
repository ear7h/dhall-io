{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Prelude hiding (IOError, truncate, read, getContents, putStrLn, readFile, unlines)
import GHC.Generics

import qualified System.IO.Error as HsError
import qualified GHC.IO.Exception as HsError (IOErrorType(..))

import qualified System.Posix.Files as Posix.Files
import qualified System.Posix as Posix

import System.Exit (ExitCode(..), exitWith)

import System.IO.Unsafe (unsafePerformIO)

import Data.Bifunctor (first)
import Data.Bits ((.|.))
import Data.Text (Text, pack, unpack, unlines)
import Data.Text.IO (putStrLn, readFile, getContents)
import Data.Void (Void)

import Lens.Family as Lens

import qualified Dhall
import qualified Dhall.Core
import qualified Dhall.Map
import qualified Dhall.Context
import qualified Dhall.Repl
import qualified Dhall.Parser
import qualified Dhall.Marshal.Decode
import qualified Dhall.Marshal.Decode as Decode
import Dhall.Marshal.Encode ((>|<), (>$<))
import qualified Dhall.Marshal.Encode as Encode
import Dhall (rawInput, Natural, FromDhall, ToDhall)
import Dhall.Parser (Src)
import Dhall.Core
    ( pretty
    , makeFunctionBinding
    , makeFieldSelection
    , Expr(..)
    , ReifiedNormalizer(..)
    , Var(..)
    , Const(..)
    )

data FileMode = MkFileMode
    { read :: Bool
    , write :: Bool
    , create :: Bool
    , truncate :: Bool
    , append :: Bool
    }
    deriving (Eq, Generic, Show)

instance FromDhall FileMode
instance ToDhall FileMode

data File = MkFile
    { fd :: Natural
    , name :: Text
    , inData :: Text
    , outData :: Text
    , mode :: FileMode
    }
    deriving (Eq, Generic, Show)

instance FromDhall File
instance ToDhall File


data World = MkWorld
    { time :: Natural
    , files :: [File]
    }
    deriving (Eq, Generic, Show)

instance FromDhall World
instance ToDhall World


data IOError
    = EOF
    | PermissionDenied
    | BadFD
    | Other Text
    deriving (Eq, Generic, Show)

convertIOError :: HsError.IOErrorType -> IOError
convertIOError HsError.EOF = EOF
convertIOError HsError.IllegalOperation = BadFD

tryIOError :: IO a -> IO (Either IOError a)
tryIOError m = do
    res <- HsError.tryIOError m
    return $ first f res
    where
        f = convertIOError . HsError.ioeGetErrorType

instance FromDhall IOError
instance ToDhall IOError

data WorldResult = MkWorldResult
    -- for some reason the auto-magic (Generic + FromDhall) makes
    --  Result e t = Err e | Ok t
    -- into
    --  < Err : e | Ok >
    -- which means we cant use the the result type in haskell here
    { err :: !(Maybe IOError)
    , world :: !World
    }
    deriving (Eq, Generic, Show)

instance FromDhall WorldResult
instance ToDhall WorldResult

data Syscall
    = Open Text FileMode
    | Read Natural
    | Write Natural Text
    | Close Natural
    | Exit Natural
    | Time
    deriving (Eq, Generic, Show)

instance FromDhall Syscall

ioErrorType
    = maximum $ Dhall.expected (Dhall.auto :: Dhall.Decoder IOError)

worldType
    = maximum $ Dhall.expected (Dhall.auto :: Dhall.Decoder World)

worldResultType
    = maximum $ Dhall.expected (Dhall.auto :: Dhall.Decoder WorldResult)

syscallType
    = maximum $ Dhall.expected (Dhall.auto :: Dhall.Decoder Syscall)

toNatural :: Integral a => a -> Natural
toNatural = fromIntegral

ioStep :: World -> Syscall -> IO WorldResult
ioStep w (Exit 0) = exitWith ExitSuccess
ioStep w (Exit n) = exitWith (ExitFailure $ fromIntegral n)
ioStep w (Open name mode) = do
    let openfd = Posix.openFd
            (unpack name)
            (mkOpenMode (read mode) (write mode))
            (mkMode (create mode) mode)
            (mkFlags mode)
    res <- tryIOError openfd
    return $ case res of
        Left err -> MkWorldResult { err = Just err, world = w }
        Right fd ->
            let
                newFile = MkFile
                    { fd = toNatural fd
                    , name = name
                    , inData = ""
                    , outData = ""
                    , mode = mode
                    }
            in MkWorldResult
                    { err = Nothing
                    , world = (w { files = newFile:(files w) })
                    }
    where
        mkOpenMode True True = Posix.ReadWrite
        mkOpenMode True False = Posix.ReadOnly
        mkOpenMode False True = Posix.WriteOnly


        mkFlags mode = Posix.defaultFileFlags
            { Posix.trunc = truncate mode
            , Posix.append = append mode
            }

        mkMode False _ = Nothing
        mkMode True mode = Just $
            if write mode
            then Posix.Files.ownerReadMode .|. Posix.Files.ownerWriteMode
            else Posix.Files.ownerReadMode

ioStep w (Read fdArg) = do
    let fdRead = Posix.fdRead (fromInteger $ toInteger fdArg) 1024
    res <- tryIOError fdRead
    return $ case res of
        Left err -> MkWorldResult { err = Just err, world = w }
        Right (inData, _) ->
            let wfiles = map (f inData) (files w)
            in MkWorldResult { err = Nothing, world = w { files = wfiles } }
    where
        f inData file
            | (fd file) == fdArg = file { inData = pack inData }
            | True = file

ioStep w (Write fdArg buf) = do
    let fdWrite = Posix.fdWrite (fromInteger $ toInteger fdArg) (unpack buf)
    res <- tryIOError fdWrite
    return $ case res of
        Left err -> MkWorldResult { err = Just err, world = w }
        Right _ -> MkWorldResult { err = Nothing, world = w }

ioStep w _ = return $ MkWorldResult
    { err = Nothing
    , world = w
    }

ioStepType :: Expr Src Void
ioStepType =
    Pi Nothing "_" worldType $
    Pi Nothing "_" syscallType $
    worldResultType


exprFromText :: Text -> Expr Src Void
exprFromText src = case Dhall.Parser.exprFromText "builtin" src of
    Left err -> error $ show err
    Right expr -> case assertNoImports expr of
        Left err -> error $ err
        Right expr -> expr
    where
        assertNoImports expr = traverse (\_ -> Left "has import!") expr



ioRunType :: Expr Src Void
ioRunType = exprFromText $ "(" <> (pretty ioType) <> ") -> Optional " <> (pretty ioErrorType)
    where
        worldResultType = exprFromText $ unlines $
            [ "{ value : < Err : " <> (pretty ioErrorType) <> " | Ok : {} > "
            , ", world : " <> (pretty worldType)
            , "}"
            ]
        ioType = exprFromText $ (pretty worldType) <> " -> " <> (pretty worldResultType)


startingContext = f Dhall.Context.empty
    where
        insert = Dhall.Context.insert
        f =   insert "IO/World" worldType
            . insert "IO/Syscall" syscallType
            . insert "IO/step" ioStepType
            . insert "IO/run" ioRunType

inject :: ToDhall a => a -> Expr s Void
inject = Dhall.Core.denote . (Dhall.embed Dhall.inject)

normalizer :: Expr s Void -> Maybe (Expr s Void)
normalizer (App (App (Var "IO/step") w) syscall)
    | Just w'       <- rawInput Dhall.auto w
    , Just syscall' <- rawInput Dhall.auto syscall = Just $ inject $ unsafePerformIO $ ioStep w' syscall'
normalizer (App (Var "IO/run") m) = Just $ Dhall.Core.denote $ exprFromText $ unlines $
    [ "merge"
    , "{ Ok = \\(_ : {}) -> None " <> (pretty' ioErrorType)
    , ", Err = \\(e : " <> (pretty ioErrorType) <> ") -> Some e"
    , "}"
    , "( (" <> (pretty m) <> ") " <> (pretty $ inject $ MkWorld { time = 0, files = [] }) <> ").value"
    ]
    where pretty' = pretty . Dhall.Core.denote
normalizer _ = Nothing

inputSettings = f Dhall.defaultInputSettings
    where
        f =
              Lens.set Dhall.normalizer (Just (ReifiedNormalizer (pure . normalizer)))
            . Lens.set Dhall.startingContext startingContext


run :: Text -> IO (Maybe IOError)
run file = do
    x <- Dhall.inputWithSettings inputSettings Dhall.auto ("IO/run " <> file) :: IO (Maybe IOError)
    putStrLn "done"
    return x


main :: IO ()
main = do
    n <- run "./test-io.dhall"
    putStrLn $ pack $ show n
    return ()

