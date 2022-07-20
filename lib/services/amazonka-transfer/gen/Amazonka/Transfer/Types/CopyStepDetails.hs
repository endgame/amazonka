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
-- Module      : Amazonka.Transfer.Types.CopyStepDetails
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Amazonka.Transfer.Types.CopyStepDetails where

import qualified Amazonka.Core as Core
import qualified Amazonka.Lens as Lens
import qualified Amazonka.Prelude as Prelude
import Amazonka.Transfer.Types.InputFileLocation
import Amazonka.Transfer.Types.OverwriteExisting

-- | Each step type has its own @StepDetails@ structure.
--
-- /See:/ 'newCopyStepDetails' smart constructor.
data CopyStepDetails = CopyStepDetails'
  { -- | The name of the step, used as an identifier.
    name :: Prelude.Maybe Prelude.Text,
    -- | A flag that indicates whether or not to overwrite an existing file of
    -- the same name. The default is @FALSE@.
    overwriteExisting :: Prelude.Maybe OverwriteExisting,
    destinationFileLocation :: Prelude.Maybe InputFileLocation
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'CopyStepDetails' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'name', 'copyStepDetails_name' - The name of the step, used as an identifier.
--
-- 'overwriteExisting', 'copyStepDetails_overwriteExisting' - A flag that indicates whether or not to overwrite an existing file of
-- the same name. The default is @FALSE@.
--
-- 'destinationFileLocation', 'copyStepDetails_destinationFileLocation' - Undocumented member.
newCopyStepDetails ::
  CopyStepDetails
newCopyStepDetails =
  CopyStepDetails'
    { name = Prelude.Nothing,
      overwriteExisting = Prelude.Nothing,
      destinationFileLocation = Prelude.Nothing
    }

-- | The name of the step, used as an identifier.
copyStepDetails_name :: Lens.Lens' CopyStepDetails (Prelude.Maybe Prelude.Text)
copyStepDetails_name = Lens.lens (\CopyStepDetails' {name} -> name) (\s@CopyStepDetails' {} a -> s {name = a} :: CopyStepDetails)

-- | A flag that indicates whether or not to overwrite an existing file of
-- the same name. The default is @FALSE@.
copyStepDetails_overwriteExisting :: Lens.Lens' CopyStepDetails (Prelude.Maybe OverwriteExisting)
copyStepDetails_overwriteExisting = Lens.lens (\CopyStepDetails' {overwriteExisting} -> overwriteExisting) (\s@CopyStepDetails' {} a -> s {overwriteExisting = a} :: CopyStepDetails)

-- | Undocumented member.
copyStepDetails_destinationFileLocation :: Lens.Lens' CopyStepDetails (Prelude.Maybe InputFileLocation)
copyStepDetails_destinationFileLocation = Lens.lens (\CopyStepDetails' {destinationFileLocation} -> destinationFileLocation) (\s@CopyStepDetails' {} a -> s {destinationFileLocation = a} :: CopyStepDetails)

instance Core.FromJSON CopyStepDetails where
  parseJSON =
    Core.withObject
      "CopyStepDetails"
      ( \x ->
          CopyStepDetails'
            Prelude.<$> (x Core..:? "Name")
            Prelude.<*> (x Core..:? "OverwriteExisting")
            Prelude.<*> (x Core..:? "DestinationFileLocation")
      )

instance Prelude.Hashable CopyStepDetails where
  hashWithSalt _salt CopyStepDetails' {..} =
    _salt `Prelude.hashWithSalt` name
      `Prelude.hashWithSalt` overwriteExisting
      `Prelude.hashWithSalt` destinationFileLocation

instance Prelude.NFData CopyStepDetails where
  rnf CopyStepDetails' {..} =
    Prelude.rnf name
      `Prelude.seq` Prelude.rnf overwriteExisting
      `Prelude.seq` Prelude.rnf destinationFileLocation

instance Core.ToJSON CopyStepDetails where
  toJSON CopyStepDetails' {..} =
    Core.object
      ( Prelude.catMaybes
          [ ("Name" Core..=) Prelude.<$> name,
            ("OverwriteExisting" Core..=)
              Prelude.<$> overwriteExisting,
            ("DestinationFileLocation" Core..=)
              Prelude.<$> destinationFileLocation
          ]
      )
