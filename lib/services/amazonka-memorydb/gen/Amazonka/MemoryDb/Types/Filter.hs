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
-- Module      : Amazonka.MemoryDb.Types.Filter
-- Copyright   : (c) 2013-2022 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Amazonka.MemoryDb.Types.Filter where

import qualified Amazonka.Core as Core
import qualified Amazonka.Lens as Lens
import qualified Amazonka.Prelude as Prelude

-- | Used to streamline results of a search based on the property being
-- filtered.
--
-- /See:/ 'newFilter' smart constructor.
data Filter = Filter'
  { -- | The property being filtered. For example, UserName.
    name :: Prelude.Text,
    -- | The property values to filter on. For example, \"user-123\".
    values :: Prelude.NonEmpty Prelude.Text
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'Filter' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'name', 'filter_name' - The property being filtered. For example, UserName.
--
-- 'values', 'filter_values' - The property values to filter on. For example, \"user-123\".
newFilter ::
  -- | 'name'
  Prelude.Text ->
  -- | 'values'
  Prelude.NonEmpty Prelude.Text ->
  Filter
newFilter pName_ pValues_ =
  Filter'
    { name = pName_,
      values = Lens.coerced Lens.# pValues_
    }

-- | The property being filtered. For example, UserName.
filter_name :: Lens.Lens' Filter Prelude.Text
filter_name = Lens.lens (\Filter' {name} -> name) (\s@Filter' {} a -> s {name = a} :: Filter)

-- | The property values to filter on. For example, \"user-123\".
filter_values :: Lens.Lens' Filter (Prelude.NonEmpty Prelude.Text)
filter_values = Lens.lens (\Filter' {values} -> values) (\s@Filter' {} a -> s {values = a} :: Filter) Prelude.. Lens.coerced

instance Prelude.Hashable Filter where
  hashWithSalt _salt Filter' {..} =
    _salt `Prelude.hashWithSalt` name
      `Prelude.hashWithSalt` values

instance Prelude.NFData Filter where
  rnf Filter' {..} =
    Prelude.rnf name `Prelude.seq` Prelude.rnf values

instance Core.ToJSON Filter where
  toJSON Filter' {..} =
    Core.object
      ( Prelude.catMaybes
          [ Prelude.Just ("Name" Core..= name),
            Prelude.Just ("Values" Core..= values)
          ]
      )
