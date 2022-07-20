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
-- Module      : Amazonka.MediaConvert.Types.CmafAdditionalManifest
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Amazonka.MediaConvert.Types.CmafAdditionalManifest where

import qualified Amazonka.Core as Core
import qualified Amazonka.Lens as Lens
import qualified Amazonka.Prelude as Prelude

-- | Specify the details for each pair of HLS and DASH additional manifests
-- that you want the service to generate for this CMAF output group. Each
-- pair of manifests can reference a different subset of outputs in the
-- group.
--
-- /See:/ 'newCmafAdditionalManifest' smart constructor.
data CmafAdditionalManifest = CmafAdditionalManifest'
  { -- | Specify the outputs that you want this additional top-level manifest to
    -- reference.
    selectedOutputs :: Prelude.Maybe [Prelude.Text],
    -- | Specify a name modifier that the service adds to the name of this
    -- manifest to make it different from the file names of the other main
    -- manifests in the output group. For example, say that the default main
    -- manifest for your HLS group is film-name.m3u8. If you enter
    -- \"-no-premium\" for this setting, then the file name the service
    -- generates for this top-level manifest is film-name-no-premium.m3u8. For
    -- HLS output groups, specify a manifestNameModifier that is different from
    -- the nameModifier of the output. The service uses the output name
    -- modifier to create unique names for the individual variant manifests.
    manifestNameModifier :: Prelude.Maybe Prelude.Text
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'CmafAdditionalManifest' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'selectedOutputs', 'cmafAdditionalManifest_selectedOutputs' - Specify the outputs that you want this additional top-level manifest to
-- reference.
--
-- 'manifestNameModifier', 'cmafAdditionalManifest_manifestNameModifier' - Specify a name modifier that the service adds to the name of this
-- manifest to make it different from the file names of the other main
-- manifests in the output group. For example, say that the default main
-- manifest for your HLS group is film-name.m3u8. If you enter
-- \"-no-premium\" for this setting, then the file name the service
-- generates for this top-level manifest is film-name-no-premium.m3u8. For
-- HLS output groups, specify a manifestNameModifier that is different from
-- the nameModifier of the output. The service uses the output name
-- modifier to create unique names for the individual variant manifests.
newCmafAdditionalManifest ::
  CmafAdditionalManifest
newCmafAdditionalManifest =
  CmafAdditionalManifest'
    { selectedOutputs =
        Prelude.Nothing,
      manifestNameModifier = Prelude.Nothing
    }

-- | Specify the outputs that you want this additional top-level manifest to
-- reference.
cmafAdditionalManifest_selectedOutputs :: Lens.Lens' CmafAdditionalManifest (Prelude.Maybe [Prelude.Text])
cmafAdditionalManifest_selectedOutputs = Lens.lens (\CmafAdditionalManifest' {selectedOutputs} -> selectedOutputs) (\s@CmafAdditionalManifest' {} a -> s {selectedOutputs = a} :: CmafAdditionalManifest) Prelude.. Lens.mapping Lens.coerced

-- | Specify a name modifier that the service adds to the name of this
-- manifest to make it different from the file names of the other main
-- manifests in the output group. For example, say that the default main
-- manifest for your HLS group is film-name.m3u8. If you enter
-- \"-no-premium\" for this setting, then the file name the service
-- generates for this top-level manifest is film-name-no-premium.m3u8. For
-- HLS output groups, specify a manifestNameModifier that is different from
-- the nameModifier of the output. The service uses the output name
-- modifier to create unique names for the individual variant manifests.
cmafAdditionalManifest_manifestNameModifier :: Lens.Lens' CmafAdditionalManifest (Prelude.Maybe Prelude.Text)
cmafAdditionalManifest_manifestNameModifier = Lens.lens (\CmafAdditionalManifest' {manifestNameModifier} -> manifestNameModifier) (\s@CmafAdditionalManifest' {} a -> s {manifestNameModifier = a} :: CmafAdditionalManifest)

instance Core.FromJSON CmafAdditionalManifest where
  parseJSON =
    Core.withObject
      "CmafAdditionalManifest"
      ( \x ->
          CmafAdditionalManifest'
            Prelude.<$> ( x Core..:? "selectedOutputs"
                            Core..!= Prelude.mempty
                        )
            Prelude.<*> (x Core..:? "manifestNameModifier")
      )

instance Prelude.Hashable CmafAdditionalManifest where
  hashWithSalt _salt CmafAdditionalManifest' {..} =
    _salt `Prelude.hashWithSalt` selectedOutputs
      `Prelude.hashWithSalt` manifestNameModifier

instance Prelude.NFData CmafAdditionalManifest where
  rnf CmafAdditionalManifest' {..} =
    Prelude.rnf selectedOutputs
      `Prelude.seq` Prelude.rnf manifestNameModifier

instance Core.ToJSON CmafAdditionalManifest where
  toJSON CmafAdditionalManifest' {..} =
    Core.object
      ( Prelude.catMaybes
          [ ("selectedOutputs" Core..=)
              Prelude.<$> selectedOutputs,
            ("manifestNameModifier" Core..=)
              Prelude.<$> manifestNameModifier
          ]
      )
