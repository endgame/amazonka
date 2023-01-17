{-# LANGUAGE TemplateHaskell #-}

module Gen.Types.Ann where

import qualified Control.Comonad as Comonad
import qualified Control.Comonad.Cofree as Cofree
import qualified Control.Lens as Lens
import qualified Data.Aeson as Aeson
import qualified Data.Function as Function
import qualified Data.Set as Set
import qualified Data.Text as Text
import Gen.Prelude
import Gen.TH
import Gen.Types.Id

data Direction
  = Output
  | Input
  deriving (Eq, Show, Generic)

instance Hashable Direction

data Mode
  = Bi
  | Uni !Direction
  deriving (Eq, Show)

instance Semigroup Mode where
  (Uni i) <> (Uni o)
    | i == o = Uni o
  _ <> _ = Bi

instance Monoid Mode where
  mempty = Bi
  mappend = (<>)

data Relation = Relation
  { _relShared :: Int, -- FIXME: get around to using something more sensible.
    _relMode :: Mode
  }
  deriving (Eq, Show)

$(Lens.makeClassy ''Relation)

instance Semigroup Relation where
  a <> b = Relation (Function.on add _relShared b a) (Function.on (<>) _relMode b a)
    where
      add 0 0 = 2
      add 1 0 = 2
      add 0 1 = 2
      add x y = x + y

instance Monoid Relation where
  mempty = Relation 0 mempty

instance (Functor f, HasRelation a) => HasRelation (Cofree f a) where
  relation = Lens.lens Comonad.extract (flip (:<) . Cofree.unwrap) . relation

mkRelation :: Maybe Id -> Direction -> Relation
mkRelation p = Relation (maybe 0 (const 1) p) . Uni

isShared :: HasRelation a => a -> Bool
isShared = (> 1) . Lens.view relShared

isOrphan :: HasRelation a => a -> Bool
isOrphan = (== 0) . Lens.view relShared

data Derive
  = DEq
  | DOrd
  | DRead
  | DShow
  | DEnum
  | DBounded
  | DNum
  | DIntegral
  | DReal
  | DRealFrac
  | DRealFloat
  | DMonoid
  | DSemigroup
  | DIsString
  | DGeneric
  | DHashable
  | DNFData
  deriving (Bounded, Enum, Eq, Generic, Ord, Show)

instance Hashable Derive

instance FromJSON Derive where
  parseJSON = gParseJSON' (camel & ctor %~ (. Text.drop 1))

derivingName :: Derive -> Maybe String
derivingName = \case
  DHashable -> Nothing
  DNFData -> Nothing
  other -> Just (drop 1 (show other))

-- | Primitive types in AWS service definition files.
--
-- /See:/ 'Gen.Types.Service.ShapeF' for lists/maps/structs.
data Lit
  = Int
  | Long
  | Double
  | Text
  | Base64
  | Bytes
  | Time
  | Bool
  | Json
  deriving (Eq, Show)

derivingBase, dNum, dFrac, dString, dOrd, dEnum, dJson, dStream, dMonoid :: Set Derive
derivingBase = Set.fromList [DEq, DRead, DShow, DGeneric, DHashable, DNFData]
dNum = Set.fromList [DNum, DIntegral, DReal] <> dEnum
dFrac = Set.fromList [DOrd, DRealFrac, DRealFloat]
dString = Set.fromList [DOrd, DIsString]
dOrd = Set.fromList [DOrd]
dEnum = Set.fromList [DOrd, DEnum, DBounded]
dJson = Set.fromList [DEq, DShow, DGeneric, DHashable, DNFData]
dStream = Set.fromList [DShow, DGeneric]
dMonoid = Set.fromList [DMonoid, DSemigroup]

litDerives :: Lit -> Set Derive
litDerives = \case
  Int -> derivingBase <> dNum
  Long -> derivingBase <> dNum
  Double -> derivingBase <> dFrac
  Text -> derivingBase <> dString
  Base64 -> derivingBase
  Bytes -> derivingBase
  Time -> derivingBase <> dOrd
  Bool -> derivingBase <> dEnum
  Json -> dJson
  where

data TypeF a
  = TType Text (Set Derive)
  | TLit a
  | TNatural
  | TStream
  | TMaybe (TypeF a)
  | TSensitive (TypeF a)
  | TList (TypeF a)
  | TList1 (TypeF a)
  | TMap (TypeF a) (TypeF a)
  deriving (Eq, Show, Functor)

-- FIXME: Moving to a fixpoint required too many initial changes - revisit.
type TType = TypeF Lit

ttypeDerives :: TType -> Set Derive
ttypeDerives = \case
  TType _ ds -> ds
  TLit lit -> litDerives lit
  TNatural -> litDerives Long
  TStream -> dStream
  TMaybe t -> ttypeDerives t
  TSensitive t -> Set.insert DShow . Set.delete DRead $ ttypeDerives t
  TList t -> Set.insert DMonoid $ ttypeDerives (TList1 t)
  TList1 t -> Set.insert DSemigroup $ ttypeDerives t
  TMap k v -> dMonoid <> Set.intersection (ttypeDerives k) (ttypeDerives v)

isEq, isHashable, isMonoid, isNFData :: TType -> Bool
isEq = elem DEq . ttypeDerives
isHashable = elem DHashable . ttypeDerives
isMonoid = elem DMonoid . ttypeDerives
isNFData = elem DNFData . ttypeDerives

data Related = Related
  { _annId :: Id,
    _annRelation :: Relation
  }
  deriving (Eq, Show)

$(Lens.makeClassy ''Related)

instance (Functor f, HasRelated a) => HasRelated (Cofree f a) where
  related = Lens.lens Comonad.extract (flip (:<) . Cofree.unwrap) . related

instance HasId Related where
  identifier = Lens.view annId

instance HasRelation Related where
  relation = annRelation

data Prefixed = Prefixed
  { _annRelated :: Related,
    _annPrefix :: Maybe Text
  }
  deriving (Eq, Show)

$(Lens.makeClassy ''Prefixed)

instance (Functor f, HasPrefixed a) => HasPrefixed (Cofree f a) where
  prefixed = Lens.lens Comonad.extract (flip (:<) . Cofree.unwrap) . prefixed

instance HasRelation Prefixed where
  relation = related . relation

instance HasRelated Prefixed where
  related = annRelated

instance HasId Prefixed where
  identifier = Lens.view annId

data Solved = Solved
  { _annPrefixed :: Prefixed,
    _annType :: TType
  }
  deriving (Eq, Show)

$(Lens.makeClassy ''Solved)

instance (Functor f, HasSolved a) => HasSolved (Cofree f a) where
  solved = Lens.lens Comonad.extract (flip (:<) . Cofree.unwrap) . solved

instance HasRelation Solved where
  relation = prefixed . relation

instance HasRelated Solved where
  related = prefixed . related

instance HasPrefixed Solved where
  prefixed = annPrefixed

instance HasId Solved where
  identifier = Lens.view annId
