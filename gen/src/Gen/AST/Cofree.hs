module Gen.AST.Cofree where

import qualified Control.Comonad as Comonad
import qualified Control.Lens as Lens
import qualified Control.Monad.Except as Except
import qualified Control.Monad.State.Strict as State
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Gen.Prelude
import Gen.Types

newtype Fix f = Fix (f (Fix f))

cofree :: Functor f => a -> Fix f -> Cofree f a
cofree x = go
  where
    go (Fix f) = x :< fmap go f

attach ::
  (Traversable t, HasId a, Monoid b) =>
  (a -> b -> c) ->
  Map Id b ->
  Cofree t a ->
  Cofree t c
attach ctor m = fmap go
  where
    go x = ctor x . fromMaybe mempty $ Map.lookup (identifier x) m

-- | Allows the new annotation to be memoised separately
-- from the pre-existing annotation.
annotate ::
  (Traversable t, MonadState s m, HasId a, Show b) =>
  (a -> b -> c) ->
  Lens' s (Map Id b) ->
  (Cofree t a -> m b) ->
  Cofree t a ->
  m (Cofree t c)
annotate ctor l f = sequenceA . Comonad.extend go
  where
    go x@(a :< _) = ctor a <$> memoise l f x

memoise ::
  (MonadState s m, HasId a, Show b) =>
  Lens' s (Map Id b) ->
  (a -> m b) ->
  a ->
  m b
memoise l f x = Lens.uses l (Map.lookup n) >>= maybe go pure
  where
    go = do
      r <- f x
      l %= Map.insert n r
      pure r

    n = identifier x

-- | Memoise the set of shapes constructed so far. Because we don't
-- return 'Ptr' unless we see an 'Id' for the second time in a
-- traversal, this is safe.
type MemoE = StateT (Map Id (Shape Id)) (Either String)

runMemoE :: MemoE a -> Either String a
runMemoE = flip State.evalStateT mempty

-- | Elaborate a map of 'ShapeF's into a 'Cofree' tree, by looking up
-- all references in the input map. The 'Cofree' allows us to inline
-- nested structure definitions, but mutually-recursive shape
-- references are broken by returning 'Ptr's as loop breakers.
--
-- We never return a 'Ptr' in the first layer of the 'Map''s
-- values.
elaborate ::
  Map Id (ShapeF () ()) ->
  Either String (Map Id (Shape Id))
elaborate shapeMap = runMemoE $ Map.traverseWithKey (addShape mempty) shapeMap
  where
    addShape :: Set Id -> Id -> ShapeF () () -> MemoE (Shape Id)
    addShape seen n shapeF
      | n `elem` seen =
          pure $! n :< Ptr (shapeF ^. info) (typeOf derives shapeMap n)
      | otherwise =
          State.gets (Map.lookup n) >>= \case
            Just shape -> pure shape
            Nothing -> do
              let shapeF' = addTType (typeOf derives shapeMap n) shapeF
              shape <- (n :<) <$> Lens.traverseOf references (ref (Set.insert n seen)) shapeF'
              State.modify' (Map.insert n shape)
              pure shape

    ref :: Set Id -> RefF () -> MemoE (RefF (Shape Id))
    ref seen r = do
      let n = r ^. refShape
      s <- findShape n >>= addShape seen n
      pure $ r & refAnn .~ s

    findShape :: Id -> MemoE (ShapeF () ())
    findShape n = case Map.lookup n shapeMap of
      Nothing ->
        Except.throwError $
          unwords
            [ "Missing shape ",
              Text.unpack (memberId n),
              ", possible matches: ",
              partial n shapeMap
            ]
      Just s -> pure s

    derives = shapeDerives shapeMap
