{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

-- Derived from AWS service descriptions, licensed under Apache 2.0.

-- |
-- Module      : Network.AWS.MediaConvert.Types.H264ParControl
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Network.AWS.MediaConvert.Types.H264ParControl
  ( H264ParControl
      ( ..,
        H264ParControl_INITIALIZE_FROM_SOURCE,
        H264ParControl_SPECIFIED
      ),
  )
where

import qualified Network.AWS.Prelude as Prelude

-- | Optional. Specify how the service determines the pixel aspect ratio
-- (PAR) for this output. The default behavior, Follow source
-- (INITIALIZE_FROM_SOURCE), uses the PAR from your input video for your
-- output. To specify a different PAR in the console, choose any value
-- other than Follow source. To specify a different PAR by editing the JSON
-- job specification, choose SPECIFIED. When you choose SPECIFIED for this
-- setting, you must also specify values for the parNumerator and
-- parDenominator settings.
newtype H264ParControl = H264ParControl'
  { fromH264ParControl ::
      Prelude.Text
  }
  deriving
    ( Prelude.Show,
      Prelude.Read,
      Prelude.Eq,
      Prelude.Ord,
      Prelude.Data,
      Prelude.Typeable,
      Prelude.Generic,
      Prelude.Hashable,
      Prelude.NFData,
      Prelude.FromText,
      Prelude.ToText,
      Prelude.ToByteString,
      Prelude.ToLog,
      Prelude.ToHeader,
      Prelude.ToQuery,
      Prelude.FromJSON,
      Prelude.FromJSONKey,
      Prelude.ToJSON,
      Prelude.ToJSONKey,
      Prelude.FromXML,
      Prelude.ToXML
    )

pattern H264ParControl_INITIALIZE_FROM_SOURCE :: H264ParControl
pattern H264ParControl_INITIALIZE_FROM_SOURCE = H264ParControl' "INITIALIZE_FROM_SOURCE"

pattern H264ParControl_SPECIFIED :: H264ParControl
pattern H264ParControl_SPECIFIED = H264ParControl' "SPECIFIED"

{-# COMPLETE
  H264ParControl_INITIALIZE_FROM_SOURCE,
  H264ParControl_SPECIFIED,
  H264ParControl'
  #-}
