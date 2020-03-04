{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE NoMonoLocalBinds #-}
{-# LANGUAGE TemplateHaskell #-}
module NewRules where

import Data.GADT.Show
import Data.GADT.Compare.TH
import Data.GADT.Show.TH
import Control.Error.Util
import qualified Data.Dependent.Map as D
import Data.Dependent.Map (DMap, DSum(..))
import Reflex.Time
import Reflex.Network
import System.Directory
import Reflex
import GHC hiding (parseModule, mkModule, typecheckModule, getSession)
import qualified GHC
import Reflex.PerformEvent.Class
import Development.IDE.Core.Compile
import Data.Default
import Control.Monad.IO.Class
import Development.IDE.Types.Location
import StringBuffer
import Development.IDE.Types.Options
import Development.IDE.Core.Shake (IdeResult(..))
import Data.Dependent.Map (GCompare)
import Data.GADT.Compare
import qualified Data.Map as M
import Unsafe.Coerce
import Reflex.Host.Basic
import Development.IDE.Import.FindImports
import Control.Monad
import HscTypes
import Data.Either
import Control.Monad.Trans.Maybe
import Control.Monad.Trans
import Module hiding (mkModule)
import qualified Data.Set as Set
import Data.Maybe
import Control.Monad.State.Strict
import Development.IDE.Types.Diagnostics
import Development.IDE.Import.DependencyInformation
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.Coerce
import Data.Traversable
import qualified GHC.LanguageExtensions as LangExt
import DynFlags
import Development.IDE.Spans.Type
import Development.IDE.Spans.Calculate
import HIE.Bios
import HIE.Bios.Environment
import System.Environment
import System.IO
import Linker
import qualified GHC.Paths
import Control.Concurrent
import Reflex.Profiled
import Debug.Trace

data HoverMap = HoverMap
type Diagnostics = String
type RMap t a = M.Map NormalizedFilePath (Dynamic t a)

{-
data State t = State { input :: Event t FilePath -- ^ Files which are being modified
                     , fileInputs :: Dynamic t [FilePath] -- List of current files of interest
                     , diags :: RMap t [Diagnostics] -- ^ The current diagnostics for each path
                     , hover :: RMap t HoverMap -- ^ The current hover map for each path.
                     , parsedModules :: Dynamic t (RMap t ParsedModule)
                     , dependencyInformation :: RMap t ()
                     , typecheckedModules :: RMap t TypecheckedModule
                     }
                     -}

type LocatedImports =   ([(Located ModuleName,
                              Maybe NormalizedFilePath)],
                            Set.Set InstalledUnitId)

data RuleType a where
  GetParsedModule :: RuleType ParsedModule
  GetLocatedImports :: RuleType LocatedImports
  GetSpanInfo :: RuleType SpansInfo
  GetDependencyInfo :: RuleType DependencyInformation
  GetDependencies :: RuleType TransitiveDependencies
  GetTypecheckedModule :: RuleType TcModuleResult

concat <$> sequence [deriveGEq ''RuleType, deriveGCompare ''RuleType, deriveGShow ''RuleType]




newtype MDynamic t a = MDynamic { getMD :: Dynamic t (Maybe a) }

data ModuleState t = ModuleState { rules :: DMap RuleType (MDynamic t) }

{-
data ModuleState t = ModuleState { fileChanged :: Event t NormalizedFilePath
                               , getParsedModule :: Dynamic t (Maybe ParsedModule)
                               , getLocatedImports :: Dynamic t (Maybe LocatedImports)
                               , getSpanInfo :: Dynamic t (Maybe SpansInfo)
                               , getDependencyInformation :: Dynamic t (Maybe DependencyInformation)
                               , getDependencies :: Dynamic t (Maybe TransitiveDependencies)
                               , getTypecheckedModule :: Dynamic t (Maybe TcModuleResult)
                               }
                               -}

data GlobalEnv t = GlobalEnv { opts :: (Dynamic t IdeOptions)
                             , env :: (Dynamic t HscEnv) }

type ModuleMap t = (Dynamic t (M.Map NormalizedFilePath (ModuleState t)))

data ModuleMapWithUpdater t =
  MMU {
    getMap :: ModuleMap t
    , updateMap :: [NormalizedFilePath] -> IO ()
    }

currentMap = current . getMap
updatedMap = updated . getMap


modules = map toNormalizedFilePath ["A.hs", "B.hs"]

singleton x = [x]

mkModuleMap :: forall t m . (_ ) => Dynamic t IdeOptions
                 -> Dynamic t HscEnv
                 -> Event t NormalizedFilePath
                 -> m (ModuleMap t)
mkModuleMap o e input = mdo
  -- An event which is triggered to update the incremental
  (map_update, update_trigger) <- newTriggerEvent
  map_update' <- fmap concat <$> batchOccurrences 0.01 map_update
  let mk_patch ((fp, v), _) = v
      mkM fp = (fp, Just (mkModule o e (MMU mod_map update_trigger) fp))
      mk_module fp act _ = mk_patch <$> act
      inp = M.fromList . map mkM <$> mergeWith (++) [(singleton <$> input), map_update']
--  let input_event = (fmap mk_patch . mkModule o e mod_map <$> input)

  mod_map <- listWithKeyShallowDiff M.empty inp mk_module  --(mergeWith (<>) [input_event, map_update])

  return mod_map

type Action t m a = NormalizedFilePath -> GlobalEnv t -> ModuleMapWithUpdater t -> MaybeT m (IdeResult a)

newtype WrappedAction m t a = WrappedAction { getAction :: Action t m a }

type Definition f t  = D.DSum RuleType (f t)

type ShakeDefinition m t = Definition (WrappedAction m) t

define :: RuleType a -> Action t m a -> ShakeDefinition m t
define rn a = rn :=> WrappedAction a

mkModule :: forall t m . _ => Dynamic t IdeOptions
              -> Dynamic t HscEnv
              -> ModuleMapWithUpdater t
              -> NormalizedFilePath
              -> m ((NormalizedFilePath, ModuleState t), Dynamic t [FileDiagnostic])
mkModule opts env mm f = runDynamicWriterT $ do
  -- List of all rules in the application
  let rules_raw = [getParsedModuleRule
                  , getLocatedImportsRule
                  , getDependencyInformationRule
                  , getDependenciesRule
                  , typeCheckRule
                  , getSpanInfoRule
                  ]

  (start, trigger) <- newTriggerEvent
  rule_dyns <- mapM (rule start) rules_raw
  -- Run all the rules once to get them going
  liftIO $ trigger ()

--  let diags = distributeListOverDyn [pm_diags]
  let m = ModuleState { rules = D.fromList rule_dyns }
  return (f, m)

  where
    rule trigger (name :=> (WrappedAction act)) = mdo
        let wrap = fromMaybe ([], Nothing)
        act_trig <- switchHoldPromptly trigger (fmap (\e -> leftmost [trigger, e]) deps)
        pm <- performEvent (traceAction ident (runEventWriterT (runMaybeT (act f genv mm))) <$! act_trig)
        let (act_res, deps) = splitE pm
        d <- holdDyn ([], Nothing) (wrap <$> act_res)
        let (pm_diags, res) = splitDynPure d
        tellDyn pm_diags
        let ident = show f ++ ": " ++ gshow name
        res' <- improvingMaybe res
--        return (traceDynE ("D:" ++ ident) res')
        return (name :=> MDynamic res)

    genv = GlobalEnv opts env

traceAction ident a = a
traceAction ident a = do
  liftIO $ traceEventIO ("START:" ++ ident)
  r <- a
  liftIO $ traceEventIO ("END:" ++ ident)
  return r

traceDynE p d = traceDynWith (const $ Debug.Trace.traceEvent p p) d


--test :: Dynamic t IdeOptions -> Dynamic t HscEnv -> [NormalizedFilePath] -> Event t NormalizedFilePath -> BasicGuest t m (ModuleMap t, Dynamic t [FileDiagnostic])
--test o e m i = _ $ mkModuleMap o e m i
--
-- Set the GHC libdir to the nix libdir if it's present.
getLibdir :: IO FilePath
getLibdir = fromMaybe GHC.Paths.libdir <$> lookupEnv "NIX_GHC_LIBDIR"


cradleToSession :: Cradle -> IO HscEnv
cradleToSession cradle = do
    cradleRes <- getCompilerOptions "" cradle
    ComponentOptions opts _deps <- case cradleRes of
        CradleSuccess r -> pure r
        CradleFail err -> error (show err)
        -- TODO Rather than failing here, we should ignore any files that use this cradle.
        -- That will require some more changes.
        CradleNone -> fail "'none' cradle is not yet supported"
    libdir <- getLibdir
    env <- runGhc (Just libdir) $ do
        dflags <- getSessionDynFlags
        -- Perhaps need to enable -fignore-interface-pragmas to not
        -- recompie due to changes to unfoldings and so on
        (dflags', _targets) <- addCmdOpts opts dflags
        _ <- setSessionDynFlags dflags'
        GHC.getSession

    initDynLinker env
    return env


loadSession :: FilePath -> FilePath -> IO HscEnv
loadSession dir v = do
    cradleLoc <- findCradle v
    c <- loadCradle v
    cradleToSession c


main = do
  session <- loadSession "/home/matt/reflex-ghc/ghcide/" "/home/matt/reflex-ghc/ghcide/hie.yaml"
  setCurrentDirectory "/home/matt/reflex-ghc/ghcide"
  basicHostWithQuit $ do
    pb <- getPostBuild
    (input, input_trigger) <- newTriggerEvent

    fileInputs <- holdDyn [] never
--    opts :: Dynamic t IdeOptions
    opts <- holdDyn (defaultIdeOptions undefined) never

--    env :: Dynamic t HscEnv
    env <- holdDyn session never

    mmap <- mkModuleMap opts env input
--    (mmap, diags2) <- test opts env modules input
    let diags = M.empty
        hover = M.empty
        --parsedModules = holdDyn M.empty
        dependencyInformation = M.empty
        typecheckedModules = M.empty

    performEvent_ $ liftIO . print <$> input

    liftIO $ forkIO $ do
      input_trigger (toNormalizedFilePath "src/Development/IDE/Core/Rules.hs")
      threadDelay 1000000
--      input_trigger (toNormalizedFilePath "B.hs")
      threadDelay 1000000
      showProfilingData
      threadDelay 1000000000
      liftIO $ input_trigger (toNormalizedFilePath "def")

    --performEvent_ $ liftIO . print <$> (updated diags2)
    return never


-- Typechecks a module.
typeCheckRule :: _ => ShakeDefinition m t
typeCheckRule = define GetTypecheckedModule $ \file genv ms -> do
  pm <- use_ ms GetParsedModule file
  deps <- use_ ms GetDependencies file
  packageState <- getSession genv
        -- Figure out whether we need TemplateHaskell or QuasiQuotes support
  --let graph_needs_th_qq = needsTemplateHaskellOrQQ $ hsc_mod_graph packageState
  --    file_uses_th_qq = uses_th_qq $ ms_hspp_opts (pm_mod_summary pm)
  --    any_uses_th_qq = graph_needs_th_qq || file_uses_th_qq
      {-
  tms <- if any_uses_th_qq || False
            -- If we use TH or QQ, we must obtain the bytecode
            then do
              --bytecodes <- uses_ GenerateByteCode (transitiveModuleDeps deps)
              --tmrs <- uses_ TypeCheck (transitiveModuleDeps deps)
              --pure (zipWith addByteCode bytecodes tmrs)
            else  -}
  tms <- uses_ ms GetTypecheckedModule (transitiveModuleDeps deps)
  --setPriority priorityTypeCheck
  IdeOptions{ optDefer = defer} <- getIdeOptions genv
  liftIO $ print ("typechecking", file)
  liftIO $ typecheckModule defer packageState tms pm
    where
        uses_th_qq dflags = xopt LangExt.TemplateHaskell dflags || xopt LangExt.QuasiQuotes dflags
        addByteCode :: Linkable -> TcModuleResult -> TcModuleResult
        addByteCode lm tmr = tmr { tmrModInfo = (tmrModInfo tmr) { hm_linkable = Just lm } }



getDependencyInformationRule :: _ => ShakeDefinition m t
getDependencyInformationRule = define GetDependencyInfo $ \file genv ms -> do
  (ds,rawDepInfo) <- rawDependencyInformation file genv ms
  return $ case rawDepInfo of
    Just rawDepInfo -> ([], Just $  processDependencyInformation rawDepInfo)
    Nothing -> (ds, Nothing)

rawDependencyInformation :: _ => Action t m RawDependencyInformation
rawDependencyInformation f genv ms = do
    let (initialId, initialMap) = getPathId f emptyPathIdMap
    res <- go (IntSet.singleton $ getFilePathId initialId)
       (RawDependencyInformation IntMap.empty initialMap)
    return ([], Just res)
  where
    go fs rawDepInfo =
        case IntSet.minView fs of
            -- Queue is empty
            Nothing -> pure rawDepInfo
            -- Pop f from the queue and process it
            Just (f, fs) -> do
                let fId = FilePathId f
                importsOrErr <- use ms GetLocatedImports (idToPath (rawPathIdMap rawDepInfo) fId)
                case importsOrErr of
                  Nothing ->

                    -- File doesn’t parse
                    let rawDepInfo' = insertImport fId (Left ModuleParseError) rawDepInfo
                    in do
                      go fs rawDepInfo'
                  Just (modImports, pkgImports) -> do
                    let f :: PathIdMap -> (a, Maybe NormalizedFilePath) -> (PathIdMap, (a, Maybe FilePathId))
                        f pathMap (imp, mbPath) = case mbPath of
                            Nothing -> (pathMap, (imp, Nothing))
                            Just path ->
                                let (pathId, pathMap') = getPathId path pathMap
                                in (pathMap', (imp, Just pathId))
                    -- Convert paths in imports to ids and update the path map
                    let (pathIdMap, modImports') = mapAccumL f (rawPathIdMap rawDepInfo) modImports
                    -- Files that we haven’t seen before are added to the queue.
                    let newFiles =
                            IntSet.fromList (coerce $ Data.Maybe.mapMaybe snd modImports')
                            IntSet.\\ IntMap.keysSet (rawImports rawDepInfo)
                    let rawDepInfo' = insertImport fId (Right $ ModuleImports modImports' pkgImports) rawDepInfo
                    go (newFiles `IntSet.union` fs) (rawDepInfo' { rawPathIdMap = pathIdMap })

-- returns all transitive dependencies in topological order.
-- NOTE: result does not include the argument file.
getDependenciesRule :: _ => ShakeDefinition m t
getDependenciesRule = define GetDependencies $ \fp genv ms -> do
        depInfo@DependencyInformation{..} <- use_ ms GetDependencyInfo fp
        return ([], transitiveDeps depInfo fp)

-- Source SpanInfo is used by AtPoint and Goto Definition.
getSpanInfoRule :: _ => ShakeDefinition m t
getSpanInfoRule = define GetSpanInfo $ \fp genv ms -> do
  tc <- use_ ms GetTypecheckedModule fp
  deps <- maybe (TransitiveDependencies [] []) id <$> use ms GetDependencies fp
  tms <- catMaybes <$> uses ms GetTypecheckedModule (transitiveModuleDeps deps)
  (fileImports, _) <- use_ ms GetLocatedImports fp
  packageState <- getSession genv
  x <- liftIO $ getSrcSpanInfos packageState fileImports tc tms
  return ([], Just x)

sampleMaybe :: _ => ModuleMapWithUpdater t
                 -> RuleType a
                 -> NormalizedFilePath
                 -> MaybeT m a
sampleMaybe m sel fp = do
  mm <- lift $ sample (currentMap m)
  case M.lookup fp mm of
    Just ms -> do
      d <- hoistMaybe (getMD <$> D.lookup sel (rules ms))
      lift $ tellEvent (() <$! updated d)
      MaybeT $ sample (current d)
    Nothing -> MaybeT $ do
      -- When the map updates, try again
      liftIO $ traceEventIO "FAILED TO FIND"
      tellEvent (() <$! updatedMap m)
      liftIO $ updateMap m [fp]
      return Nothing

use_ = sampleMaybe

uses_ :: _ => ModuleMapWithUpdater t
                 -> RuleType a
                 -> [NormalizedFilePath]
                 -> MaybeT m [a]
uses_ m sel fps = mapM (sampleMaybe m sel) fps

uses :: _ => ModuleMapWithUpdater t
                 -> RuleType a
                 -> [NormalizedFilePath]
                 -> MaybeT m [Maybe a]
uses m sel fps = mapM (use m sel) fps

use :: _ => ModuleMapWithUpdater t
                 -> RuleType a
                 -> NormalizedFilePath
                 -> MaybeT m (Maybe a)
use m sel fp = do
  mm <- lift $ sample (currentMap m)
  case M.lookup fp mm of
    Just ms -> do
      d <- hoistMaybe (getMD <$> D.lookup sel (rules ms))
      lift $ tellEvent (() <$! updated d)
      lift $ sample (current d)
    Nothing -> lift $ do
      liftIO $ traceEventIO "FAILED TO FIND"
      tellEvent (() <$! updatedMap m)
      liftIO $ updateMap m [fp]
      return Nothing

(<$!) v fa = fmap (\a -> a `seq` v) fa

sampleG :: _ => Dynamic t a -> MaybeT m a
sampleG d = lift $ sample (current d)

useGlobal :: (Reflex t, _) => GlobalEnv t -> (GlobalEnv t -> Dynamic t a) -> MaybeT m a
useGlobal g sel = sampleG (sel g)

getIdeOptions g = useGlobal g opts
getSession g = useGlobal g env

getLocatedImportsRule :: _ => ShakeDefinition m t
getLocatedImportsRule = define GetLocatedImports $ \file genv ms -> do
            pm <- use_ ms GetParsedModule file
            env <- getSession genv
            opt <- getIdeOptions genv
            let ms = pm_mod_summary pm
            let imports = [(False, imp) | imp <- ms_textual_imps ms] ++ [(True, imp) | imp <- ms_srcimps ms]
            let dflags = addRelativeImport file pm $ hsc_dflags env
            (diags, imports') <- lift $ fmap unzip $ forM imports $ \(isSource, (mbPkgName, modName)) -> do
                diagOrImp <- locateModule dflags (optExtensions opt) doesExist modName mbPkgName isSource
                case diagOrImp of
                    Left diags -> pure (diags, Left (modName, Nothing))
                    Right (FileImport path) -> pure ([], Left (modName, Just $ path))
                    Right (PackageImport pkgId) -> liftIO $ do
                        diagsOrPkgDeps <- computePackageDeps env pkgId
                        case diagsOrPkgDeps of
                          Left diags -> pure (diags, Right Nothing)
                          Right pkgIds -> pure ([], Right $ Just $ pkgId : pkgIds)
            let (moduleImports, pkgImports) = partitionEithers imports'
            case sequence pkgImports of
                Nothing -> pure (concat diags, Nothing)
                Just pkgImports -> pure (concat diags, Just (moduleImports, Set.fromList $ concat pkgImports))

doesExist nfp = let fp = fromNormalizedFilePath nfp in liftIO $ doesFileExist fp

-- When a new FilePath arrives we need to
-- 1. Parse the module
-- 2. Get the dependenices of the module
-- 3. Compile the dependendencies
-- 4. Compile the module
-- 5. Construct the hover map from the module
--
-- During these steps, the network should be constructed so that if
-- a new file modification event comes in, it only triggers recompilation
-- to the part of the network which may have changed.

getParsedModuleRule :: _ => ShakeDefinition m t
getParsedModuleRule = define GetParsedModule $ \fp genv ms -> do
    contents <- liftIO $ stringToStringBuffer <$> (readFile (fromNormalizedFilePath fp))
    packageState <- getSession genv
    opt <- getIdeOptions genv
    (diag, res) <- liftIO $ parseModule opt packageState (fromNormalizedFilePath fp) (Just contents)
    case res of
        Nothing -> pure (diag, Nothing)
        Just (contents, modu) -> do
            pure (diag, Just modu)
