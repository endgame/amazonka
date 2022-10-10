{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

-- Derived from AWS service descriptions, licensed under Apache 2.0.

-- |
-- Module      : Amazonka.FMS.Types.DestinationType
-- Copyright   : (c) 2013-2022 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Amazonka.FMS.Types.DestinationType
  ( DestinationType
      ( ..,
        DestinationType_IPV4,
        DestinationType_IPV6,
        DestinationType_PREFIX_LIST
      ),
  )
where

import qualified Amazonka.Core as Core
import qualified Amazonka.Prelude as Prelude

newtype DestinationType = DestinationType'
  { fromDestinationType ::
      Core.Text
  }
  deriving stock
    ( Prelude.Show,
      Prelude.Read,
      Prelude.Eq,
      Prelude.Ord,
      Prelude.Generic
    )
  deriving newtype
    ( Prelude.Hashable,
      Prelude.NFData,
      Core.FromText,
      Core.ToText,
      Core.ToByteString,
      Core.ToLog,
      Core.ToHeader,
      Core.ToQuery,
      Core.FromJSON,
      Core.FromJSONKey,
      Core.ToJSON,
      Core.ToJSONKey,
      Core.FromXML,
      Core.ToXML
    )

pattern DestinationType_IPV4 :: DestinationType
pattern DestinationType_IPV4 = DestinationType' "IPV4"

pattern DestinationType_IPV6 :: DestinationType
pattern DestinationType_IPV6 = DestinationType' "IPV6"

pattern DestinationType_PREFIX_LIST :: DestinationType
pattern DestinationType_PREFIX_LIST = DestinationType' "PREFIX_LIST"

{-# COMPLETE
  DestinationType_IPV4,
  DestinationType_IPV6,
  DestinationType_PREFIX_LIST,
  DestinationType'
  #-}
