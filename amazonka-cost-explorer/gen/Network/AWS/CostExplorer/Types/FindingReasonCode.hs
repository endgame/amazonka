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
-- Module      : Network.AWS.CostExplorer.Types.FindingReasonCode
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Network.AWS.CostExplorer.Types.FindingReasonCode
  ( FindingReasonCode
      ( ..,
        FindingReasonCode_CPU_OVER_PROVISIONED,
        FindingReasonCode_CPU_UNDER_PROVISIONED,
        FindingReasonCode_DISK_IOPS_OVER_PROVISIONED,
        FindingReasonCode_DISK_IOPS_UNDER_PROVISIONED,
        FindingReasonCode_DISK_THROUGHPUT_OVER_PROVISIONED,
        FindingReasonCode_DISK_THROUGHPUT_UNDER_PROVISIONED,
        FindingReasonCode_EBS_IOPS_OVER_PROVISIONED,
        FindingReasonCode_EBS_IOPS_UNDER_PROVISIONED,
        FindingReasonCode_EBS_THROUGHPUT_OVER_PROVISIONED,
        FindingReasonCode_EBS_THROUGHPUT_UNDER_PROVISIONED,
        FindingReasonCode_MEMORY_OVER_PROVISIONED,
        FindingReasonCode_MEMORY_UNDER_PROVISIONED,
        FindingReasonCode_NETWORK_BANDWIDTH_OVER_PROVISIONED,
        FindingReasonCode_NETWORK_BANDWIDTH_UNDER_PROVISIONED,
        FindingReasonCode_NETWORK_PPS_OVER_PROVISIONED,
        FindingReasonCode_NETWORK_PPS_UNDER_PROVISIONED
      ),
  )
where

import qualified Network.AWS.Core as Core
import qualified Network.AWS.Prelude as Prelude

newtype FindingReasonCode = FindingReasonCode'
  { fromFindingReasonCode ::
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

pattern FindingReasonCode_CPU_OVER_PROVISIONED :: FindingReasonCode
pattern FindingReasonCode_CPU_OVER_PROVISIONED = FindingReasonCode' "CPU_OVER_PROVISIONED"

pattern FindingReasonCode_CPU_UNDER_PROVISIONED :: FindingReasonCode
pattern FindingReasonCode_CPU_UNDER_PROVISIONED = FindingReasonCode' "CPU_UNDER_PROVISIONED"

pattern FindingReasonCode_DISK_IOPS_OVER_PROVISIONED :: FindingReasonCode
pattern FindingReasonCode_DISK_IOPS_OVER_PROVISIONED = FindingReasonCode' "DISK_IOPS_OVER_PROVISIONED"

pattern FindingReasonCode_DISK_IOPS_UNDER_PROVISIONED :: FindingReasonCode
pattern FindingReasonCode_DISK_IOPS_UNDER_PROVISIONED = FindingReasonCode' "DISK_IOPS_UNDER_PROVISIONED"

pattern FindingReasonCode_DISK_THROUGHPUT_OVER_PROVISIONED :: FindingReasonCode
pattern FindingReasonCode_DISK_THROUGHPUT_OVER_PROVISIONED = FindingReasonCode' "DISK_THROUGHPUT_OVER_PROVISIONED"

pattern FindingReasonCode_DISK_THROUGHPUT_UNDER_PROVISIONED :: FindingReasonCode
pattern FindingReasonCode_DISK_THROUGHPUT_UNDER_PROVISIONED = FindingReasonCode' "DISK_THROUGHPUT_UNDER_PROVISIONED"

pattern FindingReasonCode_EBS_IOPS_OVER_PROVISIONED :: FindingReasonCode
pattern FindingReasonCode_EBS_IOPS_OVER_PROVISIONED = FindingReasonCode' "EBS_IOPS_OVER_PROVISIONED"

pattern FindingReasonCode_EBS_IOPS_UNDER_PROVISIONED :: FindingReasonCode
pattern FindingReasonCode_EBS_IOPS_UNDER_PROVISIONED = FindingReasonCode' "EBS_IOPS_UNDER_PROVISIONED"

pattern FindingReasonCode_EBS_THROUGHPUT_OVER_PROVISIONED :: FindingReasonCode
pattern FindingReasonCode_EBS_THROUGHPUT_OVER_PROVISIONED = FindingReasonCode' "EBS_THROUGHPUT_OVER_PROVISIONED"

pattern FindingReasonCode_EBS_THROUGHPUT_UNDER_PROVISIONED :: FindingReasonCode
pattern FindingReasonCode_EBS_THROUGHPUT_UNDER_PROVISIONED = FindingReasonCode' "EBS_THROUGHPUT_UNDER_PROVISIONED"

pattern FindingReasonCode_MEMORY_OVER_PROVISIONED :: FindingReasonCode
pattern FindingReasonCode_MEMORY_OVER_PROVISIONED = FindingReasonCode' "MEMORY_OVER_PROVISIONED"

pattern FindingReasonCode_MEMORY_UNDER_PROVISIONED :: FindingReasonCode
pattern FindingReasonCode_MEMORY_UNDER_PROVISIONED = FindingReasonCode' "MEMORY_UNDER_PROVISIONED"

pattern FindingReasonCode_NETWORK_BANDWIDTH_OVER_PROVISIONED :: FindingReasonCode
pattern FindingReasonCode_NETWORK_BANDWIDTH_OVER_PROVISIONED = FindingReasonCode' "NETWORK_BANDWIDTH_OVER_PROVISIONED"

pattern FindingReasonCode_NETWORK_BANDWIDTH_UNDER_PROVISIONED :: FindingReasonCode
pattern FindingReasonCode_NETWORK_BANDWIDTH_UNDER_PROVISIONED = FindingReasonCode' "NETWORK_BANDWIDTH_UNDER_PROVISIONED"

pattern FindingReasonCode_NETWORK_PPS_OVER_PROVISIONED :: FindingReasonCode
pattern FindingReasonCode_NETWORK_PPS_OVER_PROVISIONED = FindingReasonCode' "NETWORK_PPS_OVER_PROVISIONED"

pattern FindingReasonCode_NETWORK_PPS_UNDER_PROVISIONED :: FindingReasonCode
pattern FindingReasonCode_NETWORK_PPS_UNDER_PROVISIONED = FindingReasonCode' "NETWORK_PPS_UNDER_PROVISIONED"

{-# COMPLETE
  FindingReasonCode_CPU_OVER_PROVISIONED,
  FindingReasonCode_CPU_UNDER_PROVISIONED,
  FindingReasonCode_DISK_IOPS_OVER_PROVISIONED,
  FindingReasonCode_DISK_IOPS_UNDER_PROVISIONED,
  FindingReasonCode_DISK_THROUGHPUT_OVER_PROVISIONED,
  FindingReasonCode_DISK_THROUGHPUT_UNDER_PROVISIONED,
  FindingReasonCode_EBS_IOPS_OVER_PROVISIONED,
  FindingReasonCode_EBS_IOPS_UNDER_PROVISIONED,
  FindingReasonCode_EBS_THROUGHPUT_OVER_PROVISIONED,
  FindingReasonCode_EBS_THROUGHPUT_UNDER_PROVISIONED,
  FindingReasonCode_MEMORY_OVER_PROVISIONED,
  FindingReasonCode_MEMORY_UNDER_PROVISIONED,
  FindingReasonCode_NETWORK_BANDWIDTH_OVER_PROVISIONED,
  FindingReasonCode_NETWORK_BANDWIDTH_UNDER_PROVISIONED,
  FindingReasonCode_NETWORK_PPS_OVER_PROVISIONED,
  FindingReasonCode_NETWORK_PPS_UNDER_PROVISIONED,
  FindingReasonCode'
  #-}