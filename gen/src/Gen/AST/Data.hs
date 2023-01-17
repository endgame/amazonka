{-# LANGUAGE ApplicativeDo #-}

module Gen.AST.Data
  ( serviceData,
    operationData,
    shapeData,
    waiterData,
  )
where

import qualified Control.Lens as Lens
import qualified Control.Monad.Trans.State as State
import qualified Data.ByteString.Char8 as ByteString.Char8
import qualified Data.Char as Char
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text.Encoding
import qualified Data.Text.Lazy as Text.Lazy
import Gen.AST.Data.Field
import Gen.AST.Data.Instance
import Gen.AST.Data.Syntax as Syntax
import Gen.Prelude
import Gen.Types
import qualified Language.Haskell.Exts as Exts
import Language.Haskell.Exts.Pretty (Pretty)

operationData ::
  Config ->
  Service Identity a (Shape b) c ->
  Operation Identity Ref (Pager Id) ->
  Either String (Operation Identity SData (Pager Id))
operationData cfg svc o = do
  (xa, x) <- struct (xr ^. refAnn)
  (ya, y) <- struct (yr ^. refAnn)

  (xd, xs) <- prodData svc xa x
  (yd, ys) <- prodData svc ya y

  xis <- addInstances (_annType xa) xs <$> requestInsts svc (_opName o) h xr xs

  cls <- pp Print $ requestD cfg svc h (xr, xis) (yr, ys)
  mpage <- pagerFields svc o >>= traverse (pp Print . pagerD xn)

  yis' <- renderInsts p yn (responseInsts ys)
  xis' <-
    maybe id (Map.insert "AWSPager") mpage
      . Map.insert "AWSRequest" cls
      <$> renderInsts p xn xis

  pure
    $! o
      { _opInput = Identity $ Prod (xa & relShared .~ 0) xd xis',
        _opOutput = Identity $ Prod ya yd yis'
      }
  where
    struct (a :< Struct _ s) = Right (a, s)
    struct _s =
      Left $
        "Unexpected non-struct shape for operation "
          ++ Text.unpack (memberId xn)

    p = svc ^. protocol
    h = o ^. opHttp

    xr = o ^. opInput . _Identity
    yr = o ^. opOutput . _Identity

    xn = identifier xr
    yn = identifier yr

shapeData ::
  Service Identity a (Shape b) c ->
  Shape Solved ->
  Either String (Maybe SData)
shapeData svc (a :< s) = case s of
  _ | s ^. infoException -> Just <$> errorData svc a (s ^. info)
  Enum i _ vs -> Just <$> sumData p a i vs
  Struct _ st -> do
    (d, fs) <- prodData svc a st
    is <-
      renderInsts p (a ^. annId) $
        addInstances (_annType a) fs (shapeInsts p r fs)
    pure $! Just $ Prod a d is
  _ -> pure Nothing
  where
    p = svc ^. metadata . protocol
    r = a ^. relMode

addInstances :: TType -> [Field] -> [Inst] -> [Inst]
addInstances ttype fs =
  cons isHashable (IsHashable fs)
    . cons isNFData (IsNFData fs)
  where
    cons predicate x
      | predicate ttype = (x :)
      | otherwise = id

errorData ::
  HasMetadata a Identity =>
  a ->
  Solved ->
  Info ->
  Either String SData
errorData m s i = Fun <$> mk
  where
    mk =
      Fun' p help
        <$> pp None (errorS p)
        <*> pp Print (errorD m p status code)
        <*> pure mempty

    help =
      flip fromMaybe (i ^. infoDocumentation)
        . fromString
        $ "Prism for " ++ Text.unpack (memberId n) ++ "' errors."

    status = i ^? infoError . Lens._Just . errStatus
    code = fromMaybe (memberId n) (i ^. infoError . Lens._Just . errCode)

    p = Text.cons '_' (typeId n)
    n = s ^. annId

sumData ::
  Protocol ->
  Solved ->
  Info ->
  Map Id Text ->
  Either String SData
sumData p s i vs = Sum s <$> mk <*> fmap Map.keys insts
  where
    mk =
      Sum' (typeId n) (i ^. infoDocumentation)
        <$> pp Print datatype
        <*> pure ctor
        <*> pure branches

    datatype =
      Exts.DataDecl
        ()
        (Exts.NewType ())
        Nothing
        (Exts.DHead () (ident (typeId n)))
        [conD newt]
        []

    newt =
      Exts.RecDecl
        ()
        (ident ctor)
        [ Exts.FieldDecl () [ident ("from" <> typeId n)] (tycon "Data.Text")
        ]

    -- Sometimes the values share a name with a type, so we prime the
    -- data constructor to avoid clashes.
    ctor = ((<> "'") . typeId) n

    insts = renderInsts p n $ shapeInsts p (s ^. relMode) []

    branches = vs & kvTraversal %~ first (branchId (s ^. annPrefix))

    n = s ^. annId

prodData ::
  Service Identity a (Shape b) c ->
  Solved ->
  StructF (Shape Solved) ->
  Either String (Prod, [Field])
prodData svc s st = (,fields) <$> mk
  where
    mk = do
      _prodDecl <- declaration
      _prodBootDecl <- bootDeclaration
      _prodCtor <- mkCtor
      _prodLenses <- traverse mkLens fields

      pure $ Prod' {..}
      where
        _prodName = typeId n
        _prodDoc = st ^. infoDocumentation
        _prodDeps = dependencies

    declaration = do
      decl <- datatype
      sels <- sequenceA selectors
      derv <- derivings

      pure $
        Text.Lazy.unlines
          [ decl,
            "    {",
            Text.Lazy.unlines sels,
            "    } " <> derv
          ]

    bootDeclaration = do
      decl <-
        pp None $
          Exts.DataDecl
            ()
            (Exts.DataType ())
            Nothing
            (Exts.DHead () (ident (typeId n)))
            []
            []
      -- Instance declarations for instances we derive in the real .hs file.
      let derives = ttypeDerives $ s ^. annType
      derivedInsts <- for (mapMaybe deriveInstHead $ toList derives) $ \h ->
        pp None $
          Exts.InstDecl
            ()
            Nothing
            ( Exts.IRule () Nothing Nothing $
                Exts.IHApp () h (Exts.TyCon () . unqual $ typeId n)
            )
            Nothing

      -- Instance declarations which are generated from the Inst data type
      let insts =
            concat
              [ shapeInsts (svc ^. protocol) (s ^. relMode) [],
                -- Handle the two oddballs that switch from Derive to
                -- Inst halfway through generation.
                [IsNFData [] | DNFData <- toList derives],
                [IsHashable [] | DHashable <- toList derives]
              ]
      instInsts <- for insts $ \inst ->
        pp None $ instD (instToQualifiedText inst) n Nothing

      pure . Text.Lazy.unlines $ [decl] ++ derivedInsts ++ instInsts

    datatype =
      pp None $
        Exts.DataDecl
          ()
          (Exts.DataType ())
          Nothing
          (Exts.DHead () (ident (typeId n)))
          [recordD svc n []]
          []

    selectors =
      case fields of
        x : xs -> selector False x : map (selector True) xs
        [] -> []
      where
        selector comma f = do
          doc <- pp None (Exts.FieldDecl () [ident (fieldAccessor f)] (Syntax.internal svc f))
          pure (annotate f <> "    " <> (if comma then ", " else "") <> doc)

        annotate f =
          maybe mempty (renderHaddock True 4) $
            f ^. fieldRef . refDocumentation

    derivings =
      pp None
        . Exts.Deriving () Nothing
        . map (Exts.IRule () Nothing Nothing)
        . mapMaybe deriveInstHead
        . toList
        . ttypeDerives
        $ _annType s

    deriveInstHead :: Derive -> Maybe (Exts.InstHead ())
    deriveInstHead d = do
      name <- derivingName d
      pure $ Exts.IHCon () $ unqual $ ("Prelude." <>) $ Text.pack name

    fields :: [Field]
    fields = mkFields svc s st

    mkLens :: Field -> Either String Fun
    mkLens f =
      Fun' (fieldLens f) (fieldHelp f)
        <$> pp None (lensS svc (s ^. annType) f)
        <*> pp None (lensD n f)
        <*> pure (Text.Lazy.fromStrict (fieldAccessor f))

    mkCtor :: Either String Fun
    mkCtor =
      Fun' (smartCtorId n) mkHelp
        <$> (pp None (ctorS svc n fields) <&> addParamComments fields)
        <*> pp Print (ctorD n fields)
        <*> pure mempty

    mkHelp :: Help
    mkHelp =
      Help $
        "Create a value of '"
          <> typeId n
          <> "' with all optional fields omitted."

    -- FIXME: dirty hack to render smart ctor parameter haddock comments.
    addParamComments :: [Field] -> Rendered -> Rendered
    addParamComments fs =
      Text.Lazy.replace " :: " "\n    :: "
        . Text.Lazy.intercalate "\n    -> "
        . zipWith rel ps
        . map Text.Lazy.strip
        . Text.Lazy.splitOn "->"
      where
        rel Nothing t = t
        rel (Just p) t = t <> " -- ^ '" <> Text.Lazy.fromStrict (fieldAccessor p) <> "'"

        ps = map Just (filter fieldIsParam fs) ++ repeat Nothing

    dependencies = foldMap (go . _fieldTType) fields
      where
        go :: TType -> Set.Set Text
        go = \case
          TType x _ -> tTypeDep x
          TLit _ -> Set.empty
          TNatural -> Set.empty
          TStream -> Set.empty
          TMaybe x -> go x
          TSensitive x -> go x
          TList x -> go x
          TList1 x -> go x
          TMap k v -> go k <> go v

        tTypeDep :: Text -> Set.Set Text
        tTypeDep x =
          if (stripped /= typeId n)
            then Set.singleton stripped
            else Set.empty
          where
            stripped = fromMaybe x $ Text.stripPrefix "(Maybe " =<< Text.stripSuffix ")" x

    n = s ^. annId

renderInsts :: Protocol -> Id -> [Inst] -> Either String (Map Text Text.Lazy.Text)
renderInsts p n = fmap Map.fromList . traverse go
  where
    go i = (instToText i,) <$> pp Print (instanceD p n i)

serviceData ::
  HasMetadata a Identity =>
  a ->
  Retry ->
  Either String Fun
serviceData m r =
  Fun' (m ^. serviceConfig) help
    <$> pp None (serviceS m)
    <*> pp Print (serviceD m r)
    <*> pure mempty
  where
    help =
      Help $
        "API version @"
          <> (m ^. apiVersion)
          <> "@ of the "
          <> (m ^. serviceFullName)
          <> " configuration."

waiterData ::
  Service Identity a (Shape b) c ->
  Map Id (Operation Identity Ref d) ->
  Id ->
  Waiter Id ->
  Either String WData
waiterData svc os n w = do
  o <- note (missingErr key (_opName <$> os)) $ Map.lookup key os
  wf <- waiterFields svc o w
  c <-
    Fun' (smartCtorId n) help
      <$> pp None (waiterS n wf)
      <*> pp Print (waiterD n wf)
      <*> pure mempty

  pure $! WData (typeId n) (_opName o) c
  where
    missingErr i xs =
      "Missing operation "
        ++ Text.unpack (memberId i)
        ++ " when rendering waiter "
        ++ ", possible matches: "
        ++ partial i xs

    help =
      Help $
        "Polls 'Amazonka."
          <> (svc ^. serviceAbbrev)
          <> "."
          <> typeId key
          <> "' every "
          <> fromString (show (_waitDelay w))
          <> " seconds until a "
          <> "successful state is reached. An error is returned after "
          <> fromString (show (_waitAttempts w))
          <> " failed checks."

    key = _waitOperation w

waiterFields ::
  Service Identity a (Shape b) c ->
  Operation Identity Ref d ->
  Waiter Id ->
  Either String (Waiter Field)
waiterFields svc o = Lens.traverseOf (waitAcceptors . Lens.each) go
  where
    out = o ^. opOutput . _Identity . refAnn

    go :: Accept Id -> Either String (Accept Field)
    go x = do
      n <- traverse (notation svc out) (x ^. acceptArgument)
      pure $! x & acceptArgument .~ n

pagerFields ::
  Service Identity a (Shape b) c ->
  Operation Identity Ref (Pager Id) ->
  Either String (Maybe (Pager Field))
pagerFields svc o = traverse go (o ^. opPager)
  where
    inp = o ^. opInput . _Identity . refAnn
    out = o ^. opOutput . _Identity . refAnn

    go :: Pager Id -> Either String (Pager Field)
    go = \case
      Only t -> Only <$> token t
      Next ks t -> Next <$> traverse (notation svc out) ks <*> token t
      Many k ts -> Many <$> notation svc out k <*> traverse token ts

    token :: Token Id -> Either String (Token Field)
    token (Token x y) =
      Token
        <$> notation svc inp x
        <*> notation svc out y

notation ::
  Service Identity a (Shape b) c ->
  Shape Solved ->
  Notation Id ->
  Either String (Notation Field)
notation svc = go
  where
    go :: Shape Solved -> Notation Id -> Either String (Notation Field)
    go s = \case
      Access ks -> Access <$> deref ks
      IsEmptyList ks -> NonEmptyList <$> deref ks
      NonEmptyList ks -> NonEmptyList <$> deref ks
      NonEmptyText k -> NonEmptyText <$> key s k
      Choice x y -> Choice <$> go s x <*> go s y
      where
        deref ks =
          flip State.evalStateT s . forM ks $ \x -> do
            k <- State.get >>= lift . (`key` x)
            State.put (skip (shape k))
            pure k

    key :: Shape Solved -> Key Id -> Either String (Key Field)
    key s = \case
      Key n -> Key <$> field' n s
      Each n -> Each <$> field' n s
      Last n -> Last <$> field' n s

    field' :: Id -> Shape Solved -> Either String Field
    field' n = \case
      a :< Struct _ st ->
        note (missingErr n (identifier a) (Map.keys (st ^. members)))
          . List.find ((n ==) . _fieldId)
          $ mkFields svc a st
      _ -> Left (descendErr n)

    shape :: Key Field -> Shape Solved
    shape =
      Lens.view (fieldRef . refAnn) . \case
        Key f -> f
        Each f -> f
        Last f -> f

    skip :: Shape a -> Shape a
    skip = \case
      _ :< List _ x -> x ^. listItem . refAnn
      _ :< Map _ x -> x ^. mapValue . refAnn
      x -> x

    missingErr a b xs =
      "Unable to find "
        ++ Text.unpack (memberId a)
        ++ " in members of "
        ++ Text.unpack (memberId b)
        ++ " "
        ++ show xs

    descendErr n =
      "Unable to descend into nested reference "
        ++ Text.unpack (memberId n)

data PP
  = Print
  | None
  deriving (Eq)

pp :: Pretty a => PP -> a -> Either String Rendered
pp i d
  | otherwise = pure (Text.Lazy.fromStrict (Text.Encoding.decodeUtf8 printed))
  where
    printed =
      ByteString.Char8.dropWhile Char.isSpace . ByteString.Char8.pack $
        Exts.prettyPrintStyleMode style mode d

    style =
      Exts.style
        { Exts.mode = Exts.PageMode,
          Exts.lineLength = 80,
          Exts.ribbonsPerLine = 1.5
        }

    mode
      | i == Print = Exts.defaultMode
      | otherwise =
        Exts.defaultMode
          { Exts.layout = Exts.PPNoLayout,
            Exts.spacing = False
          }
