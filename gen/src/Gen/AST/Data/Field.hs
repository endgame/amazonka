{-# LANGUAGE TemplateHaskell #-}

module Gen.AST.Data.Field where

import qualified Control.Comonad.Cofree as Cofree
import qualified Control.Lens as Lens
import qualified Data.Map.Strict as Map
import qualified Data.List as List
import qualified Data.Ord as Ord
import qualified Data.Text as Text
import Gen.Prelude
import Gen.Text
import Gen.Types
import Language.Haskell.Exts.Syntax (Name (..))

-- | Convenience type to package up some information from the struct with the
-- related field, namely the memberId and the (Set.member required).
data Field = Field
  { _fieldMeta :: Metadata Identity,
    _fieldOrdinal :: Int,
    -- | The memberId from the struct members map.
    _fieldId :: Id,
    -- | The original struct member reference.
    _fieldRef :: Ref,
    -- | The type computed for this field (including final tweaks like
    -- wrapping a 'TMaybe' around optional fields).
    _fieldTType :: TType,
    -- | Does the struct have this member in the required set.
    _fieldRequire :: Bool,
    -- | Does the struct have this memeber marked as the payload.
    _fieldPayload :: Bool,
    _fieldPrefix :: Maybe Text,
    _fieldNamespace :: Maybe Text,
    _fieldDirection :: Maybe Direction
  }
  deriving (Show)

$(Lens.makeLenses ''Field)

instance IsStreaming Field where
  isStreaming = isStreaming . _fieldRef

instance HasInfo Field where
  info = fieldAnn . info

-- FIXME: Can just add the metadata to field as well since
-- the protocol/timestamp are passed in everywhere in the .Syntax module.
mkFields ::
  Service Identity a (Shape b) c ->
  Solved ->
  StructF (Shape Solved) ->
  [Field]
mkFields svc s st =
  sortFields rs $ zipWith mk [1 ..] $ Map.toAscList (st ^. members)
  where
    mk :: Int -> (Id, Ref) -> Field
    mk i (k, ref) =
      Field
        { _fieldMeta = meta,
          _fieldOrdinal = i,
          _fieldId = k,
          _fieldRef = ref,
          _fieldTType = refType',
          _fieldRequire = req,
          _fieldPayload = pay,
          _fieldPrefix = p,
          _fieldNamespace = ns,
          _fieldDirection = d
        }
      where
        -- Final tweaks before generation
        refType'
          | isStreaming ref = refType
          | isKinded, isHeader = refType
          | req = refType
          | otherwise = TMaybe refType
          where
            isKinded = case refType of
              TMap {} -> True
              TList {} -> True
              _ -> False

            isHeader = ref ^. refLocation `elem` [Just Headers, Just Header]

            refType = ref ^. refAnn . Lens.to shapeTType <&> \case
                Base64 | pay -> Bytes
                lit -> lit

        req = k `elem` rs
        pay = Just k == st ^. payload

        ns =
          (Lens.view xmlUri <$> ref ^. refXMLNamespace)
            <|> (meta ^. xmlNamespace)

    meta = svc ^. metadata
    rs = st ^.. getRequired
    p = s ^. annPrefix

    d = case s ^. relMode of
      Uni x -> Just x
      Bi -> Nothing

-- | Ensures that isStreaming fields appear last in the parameter ordering.
sortFields :: [Id] -> [Field] -> [Field]
sortFields xs =
  zipWith (Lens.set fieldOrdinal) [1 ..]
    . List.sortBy (Ord.comparing isStreaming <> Ord.comparing idx)
  where
    idx x = fromMaybe (-1) (List.elemIndex (_fieldId x) xs)

fieldAnn :: Lens' Field (Shape Solved)
fieldAnn = fieldRef . refAnn

fieldLens, fieldAccessor :: Field -> Text
fieldLens f = lensId (_fieldPrefix f) (_fieldId f)
fieldAccessor f = accessorId (_fieldId f)

fieldIsParam :: Field -> Bool
fieldIsParam f = not (fieldMaybe f) && not (fieldMonoid f)

fieldParamName :: Field -> Name ()
fieldParamName =
  Ident ()
    . Text.unpack
    . Text.cons 'p'
    . flip Text.snoc '_'
    . upperHead
    . typeId
    . _fieldId

fieldHelp :: Field -> Help
fieldHelp f =
  fromMaybe def (f ^. fieldRef . refDocumentation) <> ann (_fieldTType f)
  where
    ann (TMaybe t) = ann t
    ann (TSensitive t) = ann t
    ann (TLit Base64) = base64
    ann _ = mempty

    base64 =
      "--\n-- /Note:/ This 'Lens' automatically encodes and decodes Base64 data.\n\
      \-- The underlying isomorphism will encode to Base64 representation during\n\
      \-- serialisation, and decode from Base64 representation during deserialisation.\n\
      \-- This 'Lens' accepts and returns only raw unencoded data."

    def = "Undocumented member."

fieldLocation :: Field -> Maybe Location
fieldLocation = Lens.view (fieldRef . refLocation)

-- | Is the field reference or its parent annotation streaming?
fieldStream :: Field -> Bool
fieldStream x =
  x ^. fieldRef . refStreaming
    || x ^. fieldAnn . infoStreaming

-- | Does the field have its location set to 'Body'?
fieldBody :: Field -> Bool
fieldBody x =
  case fieldLocation x of
    Just Body -> True
    Nothing -> True
    _ -> fieldStream x

-- | Is this primitive field set as the payload in the parent shape?
fieldLitPayload :: Field -> Bool
fieldLitPayload x = _fieldPayload x && (fieldLit x || fieldBytes x)

-- This is hilariously brittle.
fieldBytes :: Field -> Bool
fieldBytes = typeMember (Right Bytes) . _fieldTType

fieldMaybe :: Field -> Bool
fieldMaybe x =
  case _fieldTType x of
    TMaybe {} -> True
    _ -> False

fieldSensitive :: Field -> Bool
fieldSensitive x =
  case _fieldTType x of
    TSensitive {} -> True
    TMaybe (TSensitive {}) -> True
    _ -> False

fieldMonoid :: Field -> Bool
fieldMonoid = isMonoid . _fieldTType

-- FIXME: Do these need to consider 'Ptr's?
fieldList1, fieldList, fieldMap, fieldLit :: Field -> Bool
fieldList1 f = fieldList f && nonEmpty f
fieldList = not . Lens.isn't _List . Cofree.unwrap . Lens.view fieldAnn
fieldMap = not . Lens.isn't _Map . Cofree.unwrap . Lens.view fieldAnn
fieldLit = not . Lens.isn't _Lit . Cofree.unwrap . Lens.view fieldAnn
