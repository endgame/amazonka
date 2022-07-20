{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

-- Derived from AWS service descriptions, licensed under Apache 2.0.

-- |
-- Module      : Amazonka.SWF.RespondDecisionTaskCompleted
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
--
-- Used by deciders to tell the service that the DecisionTask identified by
-- the @taskToken@ has successfully completed. The @decisions@ argument
-- specifies the list of decisions made while processing the task.
--
-- A @DecisionTaskCompleted@ event is added to the workflow history. The
-- @executionContext@ specified is attached to the event in the workflow
-- execution history.
--
-- __Access Control__
--
-- If an IAM policy grants permission to use
-- @RespondDecisionTaskCompleted@, it can express permissions for the list
-- of decisions in the @decisions@ parameter. Each of the decisions has one
-- or more parameters, much like a regular API call. To allow for policies
-- to be as readable as possible, you can express permissions on decisions
-- as if they were actual API calls, including applying conditions to some
-- parameters. For more information, see
-- <https://docs.aws.amazon.com/amazonswf/latest/developerguide/swf-dev-iam.html Using IAM to Manage Access to Amazon SWF Workflows>
-- in the /Amazon SWF Developer Guide/.
module Amazonka.SWF.RespondDecisionTaskCompleted
  ( -- * Creating a Request
    RespondDecisionTaskCompleted (..),
    newRespondDecisionTaskCompleted,

    -- * Request Lenses
    respondDecisionTaskCompleted_executionContext,
    respondDecisionTaskCompleted_decisions,
    respondDecisionTaskCompleted_taskToken,

    -- * Destructuring the Response
    RespondDecisionTaskCompletedResponse (..),
    newRespondDecisionTaskCompletedResponse,
  )
where

import qualified Amazonka.Core as Core
import qualified Amazonka.Lens as Lens
import qualified Amazonka.Prelude as Prelude
import qualified Amazonka.Request as Request
import qualified Amazonka.Response as Response
import Amazonka.SWF.Types

-- | Input data for a TaskCompleted response to a decision task.
--
-- /See:/ 'newRespondDecisionTaskCompleted' smart constructor.
data RespondDecisionTaskCompleted = RespondDecisionTaskCompleted'
  { -- | User defined context to add to workflow execution.
    executionContext :: Prelude.Maybe Prelude.Text,
    -- | The list of decisions (possibly empty) made by the decider while
    -- processing this decision task. See the docs for the Decision structure
    -- for details.
    decisions :: Prelude.Maybe [Decision],
    -- | The @taskToken@ from the DecisionTask.
    --
    -- @taskToken@ is generated by the service and should be treated as an
    -- opaque value. If the task is passed to another process, its @taskToken@
    -- must also be passed. This enables it to provide its progress and respond
    -- with results.
    taskToken :: Prelude.Text
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'RespondDecisionTaskCompleted' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'executionContext', 'respondDecisionTaskCompleted_executionContext' - User defined context to add to workflow execution.
--
-- 'decisions', 'respondDecisionTaskCompleted_decisions' - The list of decisions (possibly empty) made by the decider while
-- processing this decision task. See the docs for the Decision structure
-- for details.
--
-- 'taskToken', 'respondDecisionTaskCompleted_taskToken' - The @taskToken@ from the DecisionTask.
--
-- @taskToken@ is generated by the service and should be treated as an
-- opaque value. If the task is passed to another process, its @taskToken@
-- must also be passed. This enables it to provide its progress and respond
-- with results.
newRespondDecisionTaskCompleted ::
  -- | 'taskToken'
  Prelude.Text ->
  RespondDecisionTaskCompleted
newRespondDecisionTaskCompleted pTaskToken_ =
  RespondDecisionTaskCompleted'
    { executionContext =
        Prelude.Nothing,
      decisions = Prelude.Nothing,
      taskToken = pTaskToken_
    }

-- | User defined context to add to workflow execution.
respondDecisionTaskCompleted_executionContext :: Lens.Lens' RespondDecisionTaskCompleted (Prelude.Maybe Prelude.Text)
respondDecisionTaskCompleted_executionContext = Lens.lens (\RespondDecisionTaskCompleted' {executionContext} -> executionContext) (\s@RespondDecisionTaskCompleted' {} a -> s {executionContext = a} :: RespondDecisionTaskCompleted)

-- | The list of decisions (possibly empty) made by the decider while
-- processing this decision task. See the docs for the Decision structure
-- for details.
respondDecisionTaskCompleted_decisions :: Lens.Lens' RespondDecisionTaskCompleted (Prelude.Maybe [Decision])
respondDecisionTaskCompleted_decisions = Lens.lens (\RespondDecisionTaskCompleted' {decisions} -> decisions) (\s@RespondDecisionTaskCompleted' {} a -> s {decisions = a} :: RespondDecisionTaskCompleted) Prelude.. Lens.mapping Lens.coerced

-- | The @taskToken@ from the DecisionTask.
--
-- @taskToken@ is generated by the service and should be treated as an
-- opaque value. If the task is passed to another process, its @taskToken@
-- must also be passed. This enables it to provide its progress and respond
-- with results.
respondDecisionTaskCompleted_taskToken :: Lens.Lens' RespondDecisionTaskCompleted Prelude.Text
respondDecisionTaskCompleted_taskToken = Lens.lens (\RespondDecisionTaskCompleted' {taskToken} -> taskToken) (\s@RespondDecisionTaskCompleted' {} a -> s {taskToken = a} :: RespondDecisionTaskCompleted)

instance Core.AWSRequest RespondDecisionTaskCompleted where
  type
    AWSResponse RespondDecisionTaskCompleted =
      RespondDecisionTaskCompletedResponse
  request = Request.postJSON defaultService
  response =
    Response.receiveNull
      RespondDecisionTaskCompletedResponse'

instance
  Prelude.Hashable
    RespondDecisionTaskCompleted
  where
  hashWithSalt _salt RespondDecisionTaskCompleted' {..} =
    _salt `Prelude.hashWithSalt` executionContext
      `Prelude.hashWithSalt` decisions
      `Prelude.hashWithSalt` taskToken

instance Prelude.NFData RespondDecisionTaskCompleted where
  rnf RespondDecisionTaskCompleted' {..} =
    Prelude.rnf executionContext
      `Prelude.seq` Prelude.rnf decisions
      `Prelude.seq` Prelude.rnf taskToken

instance Core.ToHeaders RespondDecisionTaskCompleted where
  toHeaders =
    Prelude.const
      ( Prelude.mconcat
          [ "X-Amz-Target"
              Core.=# ( "SimpleWorkflowService.RespondDecisionTaskCompleted" ::
                          Prelude.ByteString
                      ),
            "Content-Type"
              Core.=# ( "application/x-amz-json-1.0" ::
                          Prelude.ByteString
                      )
          ]
      )

instance Core.ToJSON RespondDecisionTaskCompleted where
  toJSON RespondDecisionTaskCompleted' {..} =
    Core.object
      ( Prelude.catMaybes
          [ ("executionContext" Core..=)
              Prelude.<$> executionContext,
            ("decisions" Core..=) Prelude.<$> decisions,
            Prelude.Just ("taskToken" Core..= taskToken)
          ]
      )

instance Core.ToPath RespondDecisionTaskCompleted where
  toPath = Prelude.const "/"

instance Core.ToQuery RespondDecisionTaskCompleted where
  toQuery = Prelude.const Prelude.mempty

-- | /See:/ 'newRespondDecisionTaskCompletedResponse' smart constructor.
data RespondDecisionTaskCompletedResponse = RespondDecisionTaskCompletedResponse'
  {
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'RespondDecisionTaskCompletedResponse' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
newRespondDecisionTaskCompletedResponse ::
  RespondDecisionTaskCompletedResponse
newRespondDecisionTaskCompletedResponse =
  RespondDecisionTaskCompletedResponse'

instance
  Prelude.NFData
    RespondDecisionTaskCompletedResponse
  where
  rnf _ = ()
