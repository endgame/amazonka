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
-- Module      : Network.AWS.MediaLive.Types.SmpteTtDestinationSettings
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Network.AWS.MediaLive.Types.SmpteTtDestinationSettings where

import qualified Network.AWS.Lens as Lens
import qualified Network.AWS.Prelude as Prelude

-- | Smpte Tt Destination Settings
--
-- /See:/ 'newSmpteTtDestinationSettings' smart constructor.
data SmpteTtDestinationSettings = SmpteTtDestinationSettings'
  {
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Data, Prelude.Typeable, Prelude.Generic)

-- |
-- Create a value of 'SmpteTtDestinationSettings' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
newSmpteTtDestinationSettings ::
  SmpteTtDestinationSettings
newSmpteTtDestinationSettings =
  SmpteTtDestinationSettings'

instance Prelude.FromJSON SmpteTtDestinationSettings where
  parseJSON =
    Prelude.withObject
      "SmpteTtDestinationSettings"
      (\x -> Prelude.pure SmpteTtDestinationSettings')

instance Prelude.Hashable SmpteTtDestinationSettings

instance Prelude.NFData SmpteTtDestinationSettings

instance Prelude.ToJSON SmpteTtDestinationSettings where
  toJSON =
    Prelude.const (Prelude.Object Prelude.mempty)
