{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module HeaderFileGeneration
  ( typesTable
  , headerFile
  , addVerbatimSuffix
  , addVerbatimPrefix
  , addDeclaration
  , addDeclarations
  , printDeclarations
  )
where

import Data.Functor
import Data.Map qualified as Map
import Data.Text (pack, unpack)
import Foreign.C.Types
import Foreign.Ptr
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import LatticeSymmetries.Utils (MutablePtr)
import System.Directory
import System.FilePath
import System.IO
import Prelude hiding (Type)

type TypesTable = Map Type String

data ModuleState = ModuleState
  { msTypesTable :: !TypesTable
  , msHeaderFile :: FilePath
  , msVerbatimPrefix :: [String]
  , msVerbatimSuffix :: [String]
  , msDeclarations :: [String]
  }
  deriving stock (Typeable)

putModuleState :: ModuleState -> Q ()
putModuleState = putQ

getModuleState :: Q ModuleState
getModuleState = do
  getQ >>= \case
    Just s -> pure s
    Nothing -> do
      s <- defaultModuleState
      addModFinalizer $ do
        s' <- getModuleState
        runIO $ do
          createDirectoryIfMissing True $ takeDirectory (msHeaderFile s')
          withFile (msHeaderFile s') WriteMode $ \h -> do
            hPutStr h
              . unpack
              . unlines
              . fmap pack
              $ [ "/* DO NOT MODIFY: This file is automatically generated */"
                , "#pragma once"
                , ""
                ]
              <> msVerbatimPrefix s'
              <> msDeclarations s'
              <> msVerbatimSuffix s'
      putModuleState s
      pure s

defaultModuleState :: Q ModuleState
defaultModuleState = do
  table <- Map.fromList <$> processTypePairs baseTypes
  pure
    $ ModuleState
      { msTypesTable = table
      , msHeaderFile = "dist-newstyle/foreign_stub.h"
      , msVerbatimPrefix = []
      , msVerbatimSuffix = []
      , msDeclarations = []
      }

baseTypes :: [(Q Type, String)]
baseTypes = [([t|CInt|], "int")]

typesTable :: [(Q Type, String)] -> DecsQ
typesTable pairs = do
  s <- getModuleState
  table <- Map.fromList <$> processTypePairs pairs
  putModuleState $ s {msTypesTable = table}
  pure []

headerFile :: FilePath -> DecsQ
headerFile path = do
  s <- getModuleState
  putModuleState $ s {msHeaderFile = path}
  pure []

addVerbatimPrefix :: [String] -> DecsQ
addVerbatimPrefix msg = do
  s <- getModuleState
  putModuleState $ s {msVerbatimPrefix = msVerbatimPrefix s <> msg}
  pure []

addVerbatimSuffix :: [String] -> DecsQ
addVerbatimSuffix msg = do
  s <- getModuleState
  putModuleState $ s {msVerbatimSuffix = msVerbatimSuffix s <> msg}
  pure []

addDeclaration :: String -> DecsQ
addDeclaration function = do
  s <- getModuleState
  name <- getFunctionName function
  tp <- getFunctionType name
  decl <- genCSignature function tp
  putModuleState $ s {msDeclarations = msDeclarations s <> [decl]}
  pure [ForeignD $ ExportF CCall function name tp]

addDeclarations :: [String] -> DecsQ
addDeclarations = fmap concat . mapM addDeclaration

printDeclarations :: Q ()
printDeclarations = do
  s <- getModuleState
  forM_ (msDeclarations s) $ \d ->
    runIO $ System.IO.putStrLn d

processTypePairs :: [(Q Type, String)] -> Q [(Type, String)]
processTypePairs = mapM (\(a, b) -> a <&> (,b))

lookupTypeInTable :: Type -> Q (Maybe String)
lookupTypeInTable tp = Map.lookup tp . msTypesTable <$> getModuleState

genCType :: Type -> Q String
genCType (ConT (Name (OccName "Int") _)) = pure "HsInt"
genCType tp = do
  lookupTypeInTable tp >>= \case
    Just s -> pure s
    Nothing -> do
      case tp of
        AppT cons arg -> do
          constPtr <- [t|Ptr|]
          mutablePtr <- [t|MutablePtr|]
          funPtr <- [t|FunPtr|]
          if
            | cons == constPtr -> (<> " const*") <$> genCType arg
            | cons == mutablePtr -> (<> " *") <$> genCType arg
            | cons == funPtr -> genCType arg
            | otherwise -> error $ "unknown Haskell type: " <> show tp
        _ -> error $ "unknown Haskell type: " <> show tp

getArgTypes :: Type -> [Type]
getArgTypes (AppT (AppT ArrowT arg) r) = arg : getArgTypes r
getArgTypes _ = []

getReturnType :: Type -> Q Type
getReturnType (AppT (AppT ArrowT _) r) = getReturnType r
getReturnType (AppT cons@(ConT _) arg) = do
  io <- [t|IO|]
  if cons == io
    then pure arg
    else error $ "unexpected Haskell constructor: " <> show cons
getReturnType r = pure r

getFunctionName :: String -> Q Name
getFunctionName name =
  fromMaybe (error $ "unknown Haskell value: " <> show name) <$> lookupValueName name

getFunctionType :: Name -> Q Type
getFunctionType name = do
  info <- reify name
  case info of
    VarI _ tp _ -> pure tp
    _ -> error $ "unexpected Haskell value: " <> show info

genCSignature :: String -> Type -> Q String
genCSignature name tp = do
  ret <- genCType =<< getReturnType tp
  args <- mapM genCType $ getArgTypes tp
  pure $ ret <> " " <> name <> "(" <> intercalate ", " args <> ");"
