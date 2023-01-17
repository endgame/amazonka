{-# LANGUAGE TemplateHaskell #-}

module Gen.Types.TypeOf
  ( typeOf,
    shapeDerives,
    typeDefault,
    typeMember,
  )
where

import Control.Lens (at, use, (<%=), _Just)
import Control.Lens.TH (makeLenses)
import Control.Monad.State.Strict (execState)
import Data.Foldable.WithIndex (ifor_)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Gen.Prelude
import Gen.Types.Ann
import Gen.Types.Id
import Gen.Types.Service

-- | Compute the type of a shape, in a way that does not require us to
-- first elaborate the set of shapes into the 'Cofree' structure.
--
-- See 'shapeDerives' to compute the @Map Id (Set Derive)@.
typeOf :: Map Id (Set Derive) -> Map Id (ShapeF ttype a) -> Id -> TType
typeOf derives shapeMap = go
  where
    go ident = sensitive (shape ident) $ case shape ident of
      Ptr _ ttype -> ttype
      Struct {} -> TType (typeId ident) (deriv ident)
      Enum {} -> TType (typeId ident) (deriv ident)
      List _ list@(ListF _ elements)
        | nonEmpty list -> TList1 . go $ _refShape elements
        | otherwise -> TList . go $ _refShape elements
      Map _ (MapF _ k v) ->
        case go $ _refShape k of
          TSensitive t -> TMap t . go $ _refShape v
          t -> TMap t . go $ _refShape v
      Lit inf lit -> case lit of
        Int -> natural inf $ TLit Int
        Long -> natural inf $ TLit Long
        Base64 | isStreaming inf -> TStream
        Bytes | isStreaming inf -> TStream
        _ -> TLit lit

    sensitive :: HasInfo i => i -> TType -> TType
    sensitive inf
      | inf ^. infoSensitive = TSensitive
      | otherwise = id

    shape n = case Map.lookup n shapeMap of
      Nothing -> error $ "shapeType: Missing shape " ++ show n ++ " in map"
      Just s -> s

    deriv n = case Map.lookup n derives of
      Nothing -> error $ "shapeType: Missing shape " ++ show n ++ " in derives"
      Just d -> d

    natural :: Info -> TType -> TType
    natural x
      | Just i <- x ^. infoMin, i >= 0 = const TNatural
      | otherwise = id

-- | Implement a simple propagator network for computing the set of
-- derivable classes for each 'Id'. This allows us to handle cycles in
-- our logic, like this example from @emr-containers@:
--
-- * A struct should derive the intersection of what its fields can derive
-- * A list should derive what its element type can derive, plus Monoid
-- * A @Configuration@ contains a @ConfigurationList@ contains a @Configuration@
data PropagatorState = PropagatorState
  { _cells :: Map Id (Set Derive),
    -- | Other cells to notify on an update.
    _propagators :: Map Id [(Id, Set Derive -> Set Derive)]
  }

$(makeLenses ''PropagatorState)

shapeDerives :: Map Id (ShapeF ttype a) -> Map Id (Set Derive)
shapeDerives shapeMap = _cells . flip execState initialState $ do
  setUpPropagators
  ifor_ shapeMap $ \ident -> \case
    Ptr _ typ -> addInfo ident $ ttypeDerives typ
    List {} -> pure ()
    Map {} -> pure ()
    Struct {} -> addInfo ident $ derivingBase
    Enum {} -> addInfo ident (derivingBase <> dOrd)
    Lit inf lit -> addInfo ident $ case lit of
      Base64 | isStreaming inf -> dStream
      Bytes | isStreaming inf -> dStream
      _ -> litDerives lit
  where
    initialState :: PropagatorState
    initialState =
      PropagatorState
        { _cells = universe <$ shapeMap,
          _propagators = mempty <$ shapeMap
        }

    universe :: Set Derive
    universe = Set.fromList [minBound .. maxBound]

    addInfo :: Id -> Set Derive -> State PropagatorState ()
    addInfo ident set = do
      old <- use $ cells . at ident . _Just
      new <- cells . at ident . _Just <%= Set.intersection set
      unless (old == new) $ runPropagators ident

    runPropagators :: Id -> State PropagatorState ()
    runPropagators ident = do
      set <- use $ cells . at ident . _Just
      use (propagators . at ident) >>= \case
        Nothing -> pure ()
        Just props -> for_ props $ \(dest, f) -> addInfo dest $ f set

    setUpPropagators :: State PropagatorState ()
    setUpPropagators = do
      ifor_ shapeMap $ \ident x -> do
        case x of
          Ptr {} -> pure ()
          List _ list@(ListF _ elements)
            | nonEmpty list ->
                addPropagator (_refShape elements) ident $ Set.insert DSemigroup
            | otherwise ->
                addPropagator (_refShape elements) ident $ Set.union dMonoid
          Map _ (MapF _ k v) -> do
            addPropagator (_refShape k) ident $ Set.union dMonoid
            addPropagator (_refShape v) ident $ Set.union dMonoid
          Struct _ (st@StructF {_members}) ->
            unless (isStreaming st) . for_ (_refShape <$> _members) $ \member ->
              addPropagator member ident id
          Enum {} -> pure ()
          Lit {} -> pure ()

    addPropagator :: Id -> Id -> (Set Derive -> Set Derive) -> State PropagatorState ()
    addPropagator from to f = propagators . at from . _Just %= ((to, f) :)

typeDefault :: TType -> Bool
typeDefault = \case
  TSensitive t -> typeDefault t
  TMaybe {} -> True
  TList {} -> True
  TMap {} -> True
  _ -> False

-- FIXME: This would be much more sane with a proper fixpoint datatype.
typeMember :: Either Text Lit -> TType -> Bool
typeMember x = \case
  TType t _ -> x == Left t
  TLit l -> x == Right l
  TStream -> False
  TNatural -> False
  TMaybe e -> typeMember x e
  TSensitive e -> typeMember x e
  TList e -> typeMember x e
  TList1 e -> typeMember x e
  TMap k v -> typeMember x k || typeMember x v
