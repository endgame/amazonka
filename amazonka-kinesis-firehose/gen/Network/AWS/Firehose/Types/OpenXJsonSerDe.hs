{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

-- Derived from AWS service descriptions, licensed under Apache 2.0.

-- |
-- Module      : Network.AWS.Firehose.Types.OpenXJsonSerDe
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Network.AWS.Firehose.Types.OpenXJsonSerDe where

import qualified Network.AWS.Lens as Lens
import qualified Network.AWS.Prelude as Prelude

-- | The OpenX SerDe. Used by Kinesis Data Firehose for deserializing data,
-- which means converting it from the JSON format in preparation for
-- serializing it to the Parquet or ORC format. This is one of two
-- deserializers you can choose, depending on which one offers the
-- functionality you need. The other option is the native Hive \/ HCatalog
-- JsonSerDe.
--
-- /See:/ 'newOpenXJsonSerDe' smart constructor.
data OpenXJsonSerDe = OpenXJsonSerDe'
  { -- | When set to @true@, which is the default, Kinesis Data Firehose converts
    -- JSON keys to lowercase before deserializing them.
    caseInsensitive :: Prelude.Maybe Prelude.Bool,
    -- | Maps column names to JSON keys that aren\'t identical to the column
    -- names. This is useful when the JSON contains keys that are Hive
    -- keywords. For example, @timestamp@ is a Hive keyword. If you have a JSON
    -- key named @timestamp@, set this parameter to @{\"ts\": \"timestamp\"}@
    -- to map this key to a column named @ts@.
    columnToJsonKeyMappings :: Prelude.Maybe (Prelude.HashMap Prelude.Text Prelude.Text),
    -- | When set to @true@, specifies that the names of the keys include dots
    -- and that you want Kinesis Data Firehose to replace them with
    -- underscores. This is useful because Apache Hive does not allow dots in
    -- column names. For example, if the JSON contains a key whose name is
    -- \"a.b\", you can define the column name to be \"a_b\" when using this
    -- option.
    --
    -- The default is @false@.
    convertDotsInJsonKeysToUnderscores :: Prelude.Maybe Prelude.Bool
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Data, Prelude.Typeable, Prelude.Generic)

-- |
-- Create a value of 'OpenXJsonSerDe' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'caseInsensitive', 'openXJsonSerDe_caseInsensitive' - When set to @true@, which is the default, Kinesis Data Firehose converts
-- JSON keys to lowercase before deserializing them.
--
-- 'columnToJsonKeyMappings', 'openXJsonSerDe_columnToJsonKeyMappings' - Maps column names to JSON keys that aren\'t identical to the column
-- names. This is useful when the JSON contains keys that are Hive
-- keywords. For example, @timestamp@ is a Hive keyword. If you have a JSON
-- key named @timestamp@, set this parameter to @{\"ts\": \"timestamp\"}@
-- to map this key to a column named @ts@.
--
-- 'convertDotsInJsonKeysToUnderscores', 'openXJsonSerDe_convertDotsInJsonKeysToUnderscores' - When set to @true@, specifies that the names of the keys include dots
-- and that you want Kinesis Data Firehose to replace them with
-- underscores. This is useful because Apache Hive does not allow dots in
-- column names. For example, if the JSON contains a key whose name is
-- \"a.b\", you can define the column name to be \"a_b\" when using this
-- option.
--
-- The default is @false@.
newOpenXJsonSerDe ::
  OpenXJsonSerDe
newOpenXJsonSerDe =
  OpenXJsonSerDe'
    { caseInsensitive = Prelude.Nothing,
      columnToJsonKeyMappings = Prelude.Nothing,
      convertDotsInJsonKeysToUnderscores = Prelude.Nothing
    }

-- | When set to @true@, which is the default, Kinesis Data Firehose converts
-- JSON keys to lowercase before deserializing them.
openXJsonSerDe_caseInsensitive :: Lens.Lens' OpenXJsonSerDe (Prelude.Maybe Prelude.Bool)
openXJsonSerDe_caseInsensitive = Lens.lens (\OpenXJsonSerDe' {caseInsensitive} -> caseInsensitive) (\s@OpenXJsonSerDe' {} a -> s {caseInsensitive = a} :: OpenXJsonSerDe)

-- | Maps column names to JSON keys that aren\'t identical to the column
-- names. This is useful when the JSON contains keys that are Hive
-- keywords. For example, @timestamp@ is a Hive keyword. If you have a JSON
-- key named @timestamp@, set this parameter to @{\"ts\": \"timestamp\"}@
-- to map this key to a column named @ts@.
openXJsonSerDe_columnToJsonKeyMappings :: Lens.Lens' OpenXJsonSerDe (Prelude.Maybe (Prelude.HashMap Prelude.Text Prelude.Text))
openXJsonSerDe_columnToJsonKeyMappings = Lens.lens (\OpenXJsonSerDe' {columnToJsonKeyMappings} -> columnToJsonKeyMappings) (\s@OpenXJsonSerDe' {} a -> s {columnToJsonKeyMappings = a} :: OpenXJsonSerDe) Prelude.. Lens.mapping Prelude._Coerce

-- | When set to @true@, specifies that the names of the keys include dots
-- and that you want Kinesis Data Firehose to replace them with
-- underscores. This is useful because Apache Hive does not allow dots in
-- column names. For example, if the JSON contains a key whose name is
-- \"a.b\", you can define the column name to be \"a_b\" when using this
-- option.
--
-- The default is @false@.
openXJsonSerDe_convertDotsInJsonKeysToUnderscores :: Lens.Lens' OpenXJsonSerDe (Prelude.Maybe Prelude.Bool)
openXJsonSerDe_convertDotsInJsonKeysToUnderscores = Lens.lens (\OpenXJsonSerDe' {convertDotsInJsonKeysToUnderscores} -> convertDotsInJsonKeysToUnderscores) (\s@OpenXJsonSerDe' {} a -> s {convertDotsInJsonKeysToUnderscores = a} :: OpenXJsonSerDe)

instance Prelude.FromJSON OpenXJsonSerDe where
  parseJSON =
    Prelude.withObject
      "OpenXJsonSerDe"
      ( \x ->
          OpenXJsonSerDe'
            Prelude.<$> (x Prelude..:? "CaseInsensitive")
            Prelude.<*> ( x Prelude..:? "ColumnToJsonKeyMappings"
                            Prelude..!= Prelude.mempty
                        )
            Prelude.<*> (x Prelude..:? "ConvertDotsInJsonKeysToUnderscores")
      )

instance Prelude.Hashable OpenXJsonSerDe

instance Prelude.NFData OpenXJsonSerDe

instance Prelude.ToJSON OpenXJsonSerDe where
  toJSON OpenXJsonSerDe' {..} =
    Prelude.object
      ( Prelude.catMaybes
          [ ("CaseInsensitive" Prelude..=)
              Prelude.<$> caseInsensitive,
            ("ColumnToJsonKeyMappings" Prelude..=)
              Prelude.<$> columnToJsonKeyMappings,
            ("ConvertDotsInJsonKeysToUnderscores" Prelude..=)
              Prelude.<$> convertDotsInJsonKeysToUnderscores
          ]
      )
