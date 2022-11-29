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
-- Module      : Amazonka.SWF.Types.ContinueAsNewWorkflowExecutionFailedEventAttributes
-- Copyright   : (c) 2013-2022 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Amazonka.SWF.Types.ContinueAsNewWorkflowExecutionFailedEventAttributes where

import qualified Amazonka.Core as Core
import qualified Amazonka.Core.Lens.Internal as Lens
import qualified Amazonka.Prelude as Prelude
import Amazonka.SWF.Types.ContinueAsNewWorkflowExecutionFailedCause

-- | Provides the details of the @ContinueAsNewWorkflowExecutionFailed@
-- event.
--
-- /See:/ 'newContinueAsNewWorkflowExecutionFailedEventAttributes' smart constructor.
data ContinueAsNewWorkflowExecutionFailedEventAttributes = ContinueAsNewWorkflowExecutionFailedEventAttributes'
  { -- | The cause of the failure. This information is generated by the system
    -- and can be useful for diagnostic purposes.
    --
    -- If @cause@ is set to @OPERATION_NOT_PERMITTED@, the decision failed
    -- because it lacked sufficient permissions. For details and example IAM
    -- policies, see
    -- <https://docs.aws.amazon.com/amazonswf/latest/developerguide/swf-dev-iam.html Using IAM to Manage Access to Amazon SWF Workflows>
    -- in the /Amazon SWF Developer Guide/.
    cause :: ContinueAsNewWorkflowExecutionFailedCause,
    -- | The ID of the @DecisionTaskCompleted@ event corresponding to the
    -- decision task that resulted in the @ContinueAsNewWorkflowExecution@
    -- decision that started this execution. This information can be useful for
    -- diagnosing problems by tracing back the chain of events leading up to
    -- this event.
    decisionTaskCompletedEventId :: Prelude.Integer
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'ContinueAsNewWorkflowExecutionFailedEventAttributes' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'cause', 'continueAsNewWorkflowExecutionFailedEventAttributes_cause' - The cause of the failure. This information is generated by the system
-- and can be useful for diagnostic purposes.
--
-- If @cause@ is set to @OPERATION_NOT_PERMITTED@, the decision failed
-- because it lacked sufficient permissions. For details and example IAM
-- policies, see
-- <https://docs.aws.amazon.com/amazonswf/latest/developerguide/swf-dev-iam.html Using IAM to Manage Access to Amazon SWF Workflows>
-- in the /Amazon SWF Developer Guide/.
--
-- 'decisionTaskCompletedEventId', 'continueAsNewWorkflowExecutionFailedEventAttributes_decisionTaskCompletedEventId' - The ID of the @DecisionTaskCompleted@ event corresponding to the
-- decision task that resulted in the @ContinueAsNewWorkflowExecution@
-- decision that started this execution. This information can be useful for
-- diagnosing problems by tracing back the chain of events leading up to
-- this event.
newContinueAsNewWorkflowExecutionFailedEventAttributes ::
  -- | 'cause'
  ContinueAsNewWorkflowExecutionFailedCause ->
  -- | 'decisionTaskCompletedEventId'
  Prelude.Integer ->
  ContinueAsNewWorkflowExecutionFailedEventAttributes
newContinueAsNewWorkflowExecutionFailedEventAttributes
  pCause_
  pDecisionTaskCompletedEventId_ =
    ContinueAsNewWorkflowExecutionFailedEventAttributes'
      { cause =
          pCause_,
        decisionTaskCompletedEventId =
          pDecisionTaskCompletedEventId_
      }

-- | The cause of the failure. This information is generated by the system
-- and can be useful for diagnostic purposes.
--
-- If @cause@ is set to @OPERATION_NOT_PERMITTED@, the decision failed
-- because it lacked sufficient permissions. For details and example IAM
-- policies, see
-- <https://docs.aws.amazon.com/amazonswf/latest/developerguide/swf-dev-iam.html Using IAM to Manage Access to Amazon SWF Workflows>
-- in the /Amazon SWF Developer Guide/.
continueAsNewWorkflowExecutionFailedEventAttributes_cause :: Lens.Lens' ContinueAsNewWorkflowExecutionFailedEventAttributes ContinueAsNewWorkflowExecutionFailedCause
continueAsNewWorkflowExecutionFailedEventAttributes_cause = Lens.lens (\ContinueAsNewWorkflowExecutionFailedEventAttributes' {cause} -> cause) (\s@ContinueAsNewWorkflowExecutionFailedEventAttributes' {} a -> s {cause = a} :: ContinueAsNewWorkflowExecutionFailedEventAttributes)

-- | The ID of the @DecisionTaskCompleted@ event corresponding to the
-- decision task that resulted in the @ContinueAsNewWorkflowExecution@
-- decision that started this execution. This information can be useful for
-- diagnosing problems by tracing back the chain of events leading up to
-- this event.
continueAsNewWorkflowExecutionFailedEventAttributes_decisionTaskCompletedEventId :: Lens.Lens' ContinueAsNewWorkflowExecutionFailedEventAttributes Prelude.Integer
continueAsNewWorkflowExecutionFailedEventAttributes_decisionTaskCompletedEventId = Lens.lens (\ContinueAsNewWorkflowExecutionFailedEventAttributes' {decisionTaskCompletedEventId} -> decisionTaskCompletedEventId) (\s@ContinueAsNewWorkflowExecutionFailedEventAttributes' {} a -> s {decisionTaskCompletedEventId = a} :: ContinueAsNewWorkflowExecutionFailedEventAttributes)

instance
  Core.FromJSON
    ContinueAsNewWorkflowExecutionFailedEventAttributes
  where
  parseJSON =
    Core.withObject
      "ContinueAsNewWorkflowExecutionFailedEventAttributes"
      ( \x ->
          ContinueAsNewWorkflowExecutionFailedEventAttributes'
            Prelude.<$> (x Core..: "cause")
              Prelude.<*> (x Core..: "decisionTaskCompletedEventId")
      )

instance
  Prelude.Hashable
    ContinueAsNewWorkflowExecutionFailedEventAttributes
  where
  hashWithSalt
    _salt
    ContinueAsNewWorkflowExecutionFailedEventAttributes' {..} =
      _salt `Prelude.hashWithSalt` cause
        `Prelude.hashWithSalt` decisionTaskCompletedEventId

instance
  Prelude.NFData
    ContinueAsNewWorkflowExecutionFailedEventAttributes
  where
  rnf
    ContinueAsNewWorkflowExecutionFailedEventAttributes' {..} =
      Prelude.rnf cause
        `Prelude.seq` Prelude.rnf decisionTaskCompletedEventId
