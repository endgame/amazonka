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
-- Module      : Amazonka.LexV2Models.Types.FulfillmentCodeHookSettings
-- Copyright   : (c) 2013-2022 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Amazonka.LexV2Models.Types.FulfillmentCodeHookSettings where

import qualified Amazonka.Core as Core
import qualified Amazonka.Core.Lens.Internal as Lens
import Amazonka.LexV2Models.Types.FulfillmentUpdatesSpecification
import Amazonka.LexV2Models.Types.PostFulfillmentStatusSpecification
import qualified Amazonka.Prelude as Prelude

-- | Determines if a Lambda function should be invoked for a specific intent.
--
-- /See:/ 'newFulfillmentCodeHookSettings' smart constructor.
data FulfillmentCodeHookSettings = FulfillmentCodeHookSettings'
  { -- | Determines whether the fulfillment code hook is used. When @active@ is
    -- false, the code hook doesn\'t run.
    active :: Prelude.Maybe Prelude.Bool,
    -- | Provides settings for messages sent to the user for after the Lambda
    -- fulfillment function completes. Post-fulfillment messages can be sent
    -- for both streaming and non-streaming conversations.
    postFulfillmentStatusSpecification :: Prelude.Maybe PostFulfillmentStatusSpecification,
    -- | Provides settings for update messages sent to the user for long-running
    -- Lambda fulfillment functions. Fulfillment updates can be used only with
    -- streaming conversations.
    fulfillmentUpdatesSpecification :: Prelude.Maybe FulfillmentUpdatesSpecification,
    -- | Indicates whether a Lambda function should be invoked to fulfill a
    -- specific intent.
    enabled :: Prelude.Bool
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'FulfillmentCodeHookSettings' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'active', 'fulfillmentCodeHookSettings_active' - Determines whether the fulfillment code hook is used. When @active@ is
-- false, the code hook doesn\'t run.
--
-- 'postFulfillmentStatusSpecification', 'fulfillmentCodeHookSettings_postFulfillmentStatusSpecification' - Provides settings for messages sent to the user for after the Lambda
-- fulfillment function completes. Post-fulfillment messages can be sent
-- for both streaming and non-streaming conversations.
--
-- 'fulfillmentUpdatesSpecification', 'fulfillmentCodeHookSettings_fulfillmentUpdatesSpecification' - Provides settings for update messages sent to the user for long-running
-- Lambda fulfillment functions. Fulfillment updates can be used only with
-- streaming conversations.
--
-- 'enabled', 'fulfillmentCodeHookSettings_enabled' - Indicates whether a Lambda function should be invoked to fulfill a
-- specific intent.
newFulfillmentCodeHookSettings ::
  -- | 'enabled'
  Prelude.Bool ->
  FulfillmentCodeHookSettings
newFulfillmentCodeHookSettings pEnabled_ =
  FulfillmentCodeHookSettings'
    { active =
        Prelude.Nothing,
      postFulfillmentStatusSpecification =
        Prelude.Nothing,
      fulfillmentUpdatesSpecification =
        Prelude.Nothing,
      enabled = pEnabled_
    }

-- | Determines whether the fulfillment code hook is used. When @active@ is
-- false, the code hook doesn\'t run.
fulfillmentCodeHookSettings_active :: Lens.Lens' FulfillmentCodeHookSettings (Prelude.Maybe Prelude.Bool)
fulfillmentCodeHookSettings_active = Lens.lens (\FulfillmentCodeHookSettings' {active} -> active) (\s@FulfillmentCodeHookSettings' {} a -> s {active = a} :: FulfillmentCodeHookSettings)

-- | Provides settings for messages sent to the user for after the Lambda
-- fulfillment function completes. Post-fulfillment messages can be sent
-- for both streaming and non-streaming conversations.
fulfillmentCodeHookSettings_postFulfillmentStatusSpecification :: Lens.Lens' FulfillmentCodeHookSettings (Prelude.Maybe PostFulfillmentStatusSpecification)
fulfillmentCodeHookSettings_postFulfillmentStatusSpecification = Lens.lens (\FulfillmentCodeHookSettings' {postFulfillmentStatusSpecification} -> postFulfillmentStatusSpecification) (\s@FulfillmentCodeHookSettings' {} a -> s {postFulfillmentStatusSpecification = a} :: FulfillmentCodeHookSettings)

-- | Provides settings for update messages sent to the user for long-running
-- Lambda fulfillment functions. Fulfillment updates can be used only with
-- streaming conversations.
fulfillmentCodeHookSettings_fulfillmentUpdatesSpecification :: Lens.Lens' FulfillmentCodeHookSettings (Prelude.Maybe FulfillmentUpdatesSpecification)
fulfillmentCodeHookSettings_fulfillmentUpdatesSpecification = Lens.lens (\FulfillmentCodeHookSettings' {fulfillmentUpdatesSpecification} -> fulfillmentUpdatesSpecification) (\s@FulfillmentCodeHookSettings' {} a -> s {fulfillmentUpdatesSpecification = a} :: FulfillmentCodeHookSettings)

-- | Indicates whether a Lambda function should be invoked to fulfill a
-- specific intent.
fulfillmentCodeHookSettings_enabled :: Lens.Lens' FulfillmentCodeHookSettings Prelude.Bool
fulfillmentCodeHookSettings_enabled = Lens.lens (\FulfillmentCodeHookSettings' {enabled} -> enabled) (\s@FulfillmentCodeHookSettings' {} a -> s {enabled = a} :: FulfillmentCodeHookSettings)

instance Core.FromJSON FulfillmentCodeHookSettings where
  parseJSON =
    Core.withObject
      "FulfillmentCodeHookSettings"
      ( \x ->
          FulfillmentCodeHookSettings'
            Prelude.<$> (x Core..:? "active")
            Prelude.<*> (x Core..:? "postFulfillmentStatusSpecification")
            Prelude.<*> (x Core..:? "fulfillmentUpdatesSpecification")
            Prelude.<*> (x Core..: "enabled")
      )

instance Prelude.Hashable FulfillmentCodeHookSettings where
  hashWithSalt _salt FulfillmentCodeHookSettings' {..} =
    _salt `Prelude.hashWithSalt` active
      `Prelude.hashWithSalt` postFulfillmentStatusSpecification
      `Prelude.hashWithSalt` fulfillmentUpdatesSpecification
      `Prelude.hashWithSalt` enabled

instance Prelude.NFData FulfillmentCodeHookSettings where
  rnf FulfillmentCodeHookSettings' {..} =
    Prelude.rnf active
      `Prelude.seq` Prelude.rnf postFulfillmentStatusSpecification
      `Prelude.seq` Prelude.rnf fulfillmentUpdatesSpecification
      `Prelude.seq` Prelude.rnf enabled

instance Core.ToJSON FulfillmentCodeHookSettings where
  toJSON FulfillmentCodeHookSettings' {..} =
    Core.object
      ( Prelude.catMaybes
          [ ("active" Core..=) Prelude.<$> active,
            ("postFulfillmentStatusSpecification" Core..=)
              Prelude.<$> postFulfillmentStatusSpecification,
            ("fulfillmentUpdatesSpecification" Core..=)
              Prelude.<$> fulfillmentUpdatesSpecification,
            Prelude.Just ("enabled" Core..= enabled)
          ]
      )
