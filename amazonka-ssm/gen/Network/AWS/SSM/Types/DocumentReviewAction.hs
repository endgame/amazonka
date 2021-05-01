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
-- Module      : Network.AWS.SSM.Types.DocumentReviewAction
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Network.AWS.SSM.Types.DocumentReviewAction
  ( DocumentReviewAction
      ( ..,
        DocumentReviewAction_Approve,
        DocumentReviewAction_Reject,
        DocumentReviewAction_SendForReview,
        DocumentReviewAction_UpdateReview
      ),
  )
where

import qualified Network.AWS.Prelude as Prelude

newtype DocumentReviewAction = DocumentReviewAction'
  { fromDocumentReviewAction ::
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

pattern DocumentReviewAction_Approve :: DocumentReviewAction
pattern DocumentReviewAction_Approve = DocumentReviewAction' "Approve"

pattern DocumentReviewAction_Reject :: DocumentReviewAction
pattern DocumentReviewAction_Reject = DocumentReviewAction' "Reject"

pattern DocumentReviewAction_SendForReview :: DocumentReviewAction
pattern DocumentReviewAction_SendForReview = DocumentReviewAction' "SendForReview"

pattern DocumentReviewAction_UpdateReview :: DocumentReviewAction
pattern DocumentReviewAction_UpdateReview = DocumentReviewAction' "UpdateReview"

{-# COMPLETE
  DocumentReviewAction_Approve,
  DocumentReviewAction_Reject,
  DocumentReviewAction_SendForReview,
  DocumentReviewAction_UpdateReview,
  DocumentReviewAction'
  #-}
