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
-- Module      : Amazonka.AuditManager.Types.SourceKeyword
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Amazonka.AuditManager.Types.SourceKeyword where

import Amazonka.AuditManager.Types.KeywordInputType
import qualified Amazonka.Core as Core
import qualified Amazonka.Lens as Lens
import qualified Amazonka.Prelude as Prelude

-- | The keyword to search for in CloudTrail logs, Config rules, Security Hub
-- checks, and Amazon Web Services API names.
--
-- /See:/ 'newSourceKeyword' smart constructor.
data SourceKeyword = SourceKeyword'
  { -- | The value of the keyword used to search CloudTrail logs, Config rules,
    -- Security Hub checks, and Amazon Web Services API names when mapping a
    -- control data source.
    keywordValue :: Prelude.Maybe Prelude.Text,
    -- | The method of input for the specified keyword.
    keywordInputType :: Prelude.Maybe KeywordInputType
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'SourceKeyword' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'keywordValue', 'sourceKeyword_keywordValue' - The value of the keyword used to search CloudTrail logs, Config rules,
-- Security Hub checks, and Amazon Web Services API names when mapping a
-- control data source.
--
-- 'keywordInputType', 'sourceKeyword_keywordInputType' - The method of input for the specified keyword.
newSourceKeyword ::
  SourceKeyword
newSourceKeyword =
  SourceKeyword'
    { keywordValue = Prelude.Nothing,
      keywordInputType = Prelude.Nothing
    }

-- | The value of the keyword used to search CloudTrail logs, Config rules,
-- Security Hub checks, and Amazon Web Services API names when mapping a
-- control data source.
sourceKeyword_keywordValue :: Lens.Lens' SourceKeyword (Prelude.Maybe Prelude.Text)
sourceKeyword_keywordValue = Lens.lens (\SourceKeyword' {keywordValue} -> keywordValue) (\s@SourceKeyword' {} a -> s {keywordValue = a} :: SourceKeyword)

-- | The method of input for the specified keyword.
sourceKeyword_keywordInputType :: Lens.Lens' SourceKeyword (Prelude.Maybe KeywordInputType)
sourceKeyword_keywordInputType = Lens.lens (\SourceKeyword' {keywordInputType} -> keywordInputType) (\s@SourceKeyword' {} a -> s {keywordInputType = a} :: SourceKeyword)

instance Core.FromJSON SourceKeyword where
  parseJSON =
    Core.withObject
      "SourceKeyword"
      ( \x ->
          SourceKeyword'
            Prelude.<$> (x Core..:? "keywordValue")
            Prelude.<*> (x Core..:? "keywordInputType")
      )

instance Prelude.Hashable SourceKeyword where
  hashWithSalt _salt SourceKeyword' {..} =
    _salt `Prelude.hashWithSalt` keywordValue
      `Prelude.hashWithSalt` keywordInputType

instance Prelude.NFData SourceKeyword where
  rnf SourceKeyword' {..} =
    Prelude.rnf keywordValue
      `Prelude.seq` Prelude.rnf keywordInputType

instance Core.ToJSON SourceKeyword where
  toJSON SourceKeyword' {..} =
    Core.object
      ( Prelude.catMaybes
          [ ("keywordValue" Core..=) Prelude.<$> keywordValue,
            ("keywordInputType" Core..=)
              Prelude.<$> keywordInputType
          ]
      )
