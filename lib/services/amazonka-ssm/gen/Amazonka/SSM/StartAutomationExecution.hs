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
-- Module      : Amazonka.SSM.StartAutomationExecution
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
--
-- Initiates execution of an Automation runbook.
module Amazonka.SSM.StartAutomationExecution
  ( -- * Creating a Request
    StartAutomationExecution (..),
    newStartAutomationExecution,

    -- * Request Lenses
    startAutomationExecution_tags,
    startAutomationExecution_clientToken,
    startAutomationExecution_targetLocations,
    startAutomationExecution_targetParameterName,
    startAutomationExecution_targetMaps,
    startAutomationExecution_targets,
    startAutomationExecution_maxConcurrency,
    startAutomationExecution_mode,
    startAutomationExecution_maxErrors,
    startAutomationExecution_documentVersion,
    startAutomationExecution_parameters,
    startAutomationExecution_documentName,

    -- * Destructuring the Response
    StartAutomationExecutionResponse (..),
    newStartAutomationExecutionResponse,

    -- * Response Lenses
    startAutomationExecutionResponse_automationExecutionId,
    startAutomationExecutionResponse_httpStatus,
  )
where

import qualified Amazonka.Core as Core
import qualified Amazonka.Lens as Lens
import qualified Amazonka.Prelude as Prelude
import qualified Amazonka.Request as Request
import qualified Amazonka.Response as Response
import Amazonka.SSM.Types

-- | /See:/ 'newStartAutomationExecution' smart constructor.
data StartAutomationExecution = StartAutomationExecution'
  { -- | Optional metadata that you assign to a resource. You can specify a
    -- maximum of five tags for an automation. Tags enable you to categorize a
    -- resource in different ways, such as by purpose, owner, or environment.
    -- For example, you might want to tag an automation to identify an
    -- environment or operating system. In this case, you could specify the
    -- following key-value pairs:
    --
    -- -   @Key=environment,Value=test@
    --
    -- -   @Key=OS,Value=Windows@
    --
    -- To add tags to an existing patch baseline, use the AddTagsToResource
    -- operation.
    tags :: Prelude.Maybe [Tag],
    -- | User-provided idempotency token. The token must be unique, is case
    -- insensitive, enforces the UUID format, and can\'t be reused.
    clientToken :: Prelude.Maybe Prelude.Text,
    -- | A location is a combination of Amazon Web Services Regions and\/or
    -- Amazon Web Services accounts where you want to run the automation. Use
    -- this operation to start an automation in multiple Amazon Web Services
    -- Regions and multiple Amazon Web Services accounts. For more information,
    -- see
    -- <https://docs.aws.amazon.com/systems-manager/latest/userguide/systems-manager-automation-multiple-accounts-and-regions.html Running Automation workflows in multiple Amazon Web Services Regions and Amazon Web Services accounts>
    -- in the /Amazon Web Services Systems Manager User Guide/.
    targetLocations :: Prelude.Maybe (Prelude.NonEmpty TargetLocation),
    -- | The name of the parameter used as the target resource for the
    -- rate-controlled execution. Required if you specify targets.
    targetParameterName :: Prelude.Maybe Prelude.Text,
    -- | A key-value mapping of document parameters to target resources. Both
    -- Targets and TargetMaps can\'t be specified together.
    targetMaps :: Prelude.Maybe [Prelude.HashMap Prelude.Text [Prelude.Text]],
    -- | A key-value mapping to target resources. Required if you specify
    -- TargetParameterName.
    targets :: Prelude.Maybe [Target],
    -- | The maximum number of targets allowed to run this task in parallel. You
    -- can specify a number, such as 10, or a percentage, such as 10%. The
    -- default value is @10@.
    maxConcurrency :: Prelude.Maybe Prelude.Text,
    -- | The execution mode of the automation. Valid modes include the following:
    -- Auto and Interactive. The default mode is Auto.
    mode :: Prelude.Maybe ExecutionMode,
    -- | The number of errors that are allowed before the system stops running
    -- the automation on additional targets. You can specify either an absolute
    -- number of errors, for example 10, or a percentage of the target set, for
    -- example 10%. If you specify 3, for example, the system stops running the
    -- automation when the fourth error is received. If you specify 0, then the
    -- system stops running the automation on additional targets after the
    -- first error result is returned. If you run an automation on 50 resources
    -- and set max-errors to 10%, then the system stops running the automation
    -- on additional targets when the sixth error is received.
    --
    -- Executions that are already running an automation when max-errors is
    -- reached are allowed to complete, but some of these executions may fail
    -- as well. If you need to ensure that there won\'t be more than max-errors
    -- failed executions, set max-concurrency to 1 so the executions proceed
    -- one at a time.
    maxErrors :: Prelude.Maybe Prelude.Text,
    -- | The version of the Automation runbook to use for this execution.
    documentVersion :: Prelude.Maybe Prelude.Text,
    -- | A key-value map of execution parameters, which match the declared
    -- parameters in the Automation runbook.
    parameters :: Prelude.Maybe (Prelude.HashMap Prelude.Text [Prelude.Text]),
    -- | The name of the SSM document to run. This can be a public document or a
    -- custom document. To run a shared document belonging to another account,
    -- specify the document ARN. For more information about how to use shared
    -- documents, see
    -- <https://docs.aws.amazon.com/systems-manager/latest/userguide/ssm-using-shared.html Using shared SSM documents>
    -- in the /Amazon Web Services Systems Manager User Guide/.
    documentName :: Prelude.Text
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'StartAutomationExecution' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'tags', 'startAutomationExecution_tags' - Optional metadata that you assign to a resource. You can specify a
-- maximum of five tags for an automation. Tags enable you to categorize a
-- resource in different ways, such as by purpose, owner, or environment.
-- For example, you might want to tag an automation to identify an
-- environment or operating system. In this case, you could specify the
-- following key-value pairs:
--
-- -   @Key=environment,Value=test@
--
-- -   @Key=OS,Value=Windows@
--
-- To add tags to an existing patch baseline, use the AddTagsToResource
-- operation.
--
-- 'clientToken', 'startAutomationExecution_clientToken' - User-provided idempotency token. The token must be unique, is case
-- insensitive, enforces the UUID format, and can\'t be reused.
--
-- 'targetLocations', 'startAutomationExecution_targetLocations' - A location is a combination of Amazon Web Services Regions and\/or
-- Amazon Web Services accounts where you want to run the automation. Use
-- this operation to start an automation in multiple Amazon Web Services
-- Regions and multiple Amazon Web Services accounts. For more information,
-- see
-- <https://docs.aws.amazon.com/systems-manager/latest/userguide/systems-manager-automation-multiple-accounts-and-regions.html Running Automation workflows in multiple Amazon Web Services Regions and Amazon Web Services accounts>
-- in the /Amazon Web Services Systems Manager User Guide/.
--
-- 'targetParameterName', 'startAutomationExecution_targetParameterName' - The name of the parameter used as the target resource for the
-- rate-controlled execution. Required if you specify targets.
--
-- 'targetMaps', 'startAutomationExecution_targetMaps' - A key-value mapping of document parameters to target resources. Both
-- Targets and TargetMaps can\'t be specified together.
--
-- 'targets', 'startAutomationExecution_targets' - A key-value mapping to target resources. Required if you specify
-- TargetParameterName.
--
-- 'maxConcurrency', 'startAutomationExecution_maxConcurrency' - The maximum number of targets allowed to run this task in parallel. You
-- can specify a number, such as 10, or a percentage, such as 10%. The
-- default value is @10@.
--
-- 'mode', 'startAutomationExecution_mode' - The execution mode of the automation. Valid modes include the following:
-- Auto and Interactive. The default mode is Auto.
--
-- 'maxErrors', 'startAutomationExecution_maxErrors' - The number of errors that are allowed before the system stops running
-- the automation on additional targets. You can specify either an absolute
-- number of errors, for example 10, or a percentage of the target set, for
-- example 10%. If you specify 3, for example, the system stops running the
-- automation when the fourth error is received. If you specify 0, then the
-- system stops running the automation on additional targets after the
-- first error result is returned. If you run an automation on 50 resources
-- and set max-errors to 10%, then the system stops running the automation
-- on additional targets when the sixth error is received.
--
-- Executions that are already running an automation when max-errors is
-- reached are allowed to complete, but some of these executions may fail
-- as well. If you need to ensure that there won\'t be more than max-errors
-- failed executions, set max-concurrency to 1 so the executions proceed
-- one at a time.
--
-- 'documentVersion', 'startAutomationExecution_documentVersion' - The version of the Automation runbook to use for this execution.
--
-- 'parameters', 'startAutomationExecution_parameters' - A key-value map of execution parameters, which match the declared
-- parameters in the Automation runbook.
--
-- 'documentName', 'startAutomationExecution_documentName' - The name of the SSM document to run. This can be a public document or a
-- custom document. To run a shared document belonging to another account,
-- specify the document ARN. For more information about how to use shared
-- documents, see
-- <https://docs.aws.amazon.com/systems-manager/latest/userguide/ssm-using-shared.html Using shared SSM documents>
-- in the /Amazon Web Services Systems Manager User Guide/.
newStartAutomationExecution ::
  -- | 'documentName'
  Prelude.Text ->
  StartAutomationExecution
newStartAutomationExecution pDocumentName_ =
  StartAutomationExecution'
    { tags = Prelude.Nothing,
      clientToken = Prelude.Nothing,
      targetLocations = Prelude.Nothing,
      targetParameterName = Prelude.Nothing,
      targetMaps = Prelude.Nothing,
      targets = Prelude.Nothing,
      maxConcurrency = Prelude.Nothing,
      mode = Prelude.Nothing,
      maxErrors = Prelude.Nothing,
      documentVersion = Prelude.Nothing,
      parameters = Prelude.Nothing,
      documentName = pDocumentName_
    }

-- | Optional metadata that you assign to a resource. You can specify a
-- maximum of five tags for an automation. Tags enable you to categorize a
-- resource in different ways, such as by purpose, owner, or environment.
-- For example, you might want to tag an automation to identify an
-- environment or operating system. In this case, you could specify the
-- following key-value pairs:
--
-- -   @Key=environment,Value=test@
--
-- -   @Key=OS,Value=Windows@
--
-- To add tags to an existing patch baseline, use the AddTagsToResource
-- operation.
startAutomationExecution_tags :: Lens.Lens' StartAutomationExecution (Prelude.Maybe [Tag])
startAutomationExecution_tags = Lens.lens (\StartAutomationExecution' {tags} -> tags) (\s@StartAutomationExecution' {} a -> s {tags = a} :: StartAutomationExecution) Prelude.. Lens.mapping Lens.coerced

-- | User-provided idempotency token. The token must be unique, is case
-- insensitive, enforces the UUID format, and can\'t be reused.
startAutomationExecution_clientToken :: Lens.Lens' StartAutomationExecution (Prelude.Maybe Prelude.Text)
startAutomationExecution_clientToken = Lens.lens (\StartAutomationExecution' {clientToken} -> clientToken) (\s@StartAutomationExecution' {} a -> s {clientToken = a} :: StartAutomationExecution)

-- | A location is a combination of Amazon Web Services Regions and\/or
-- Amazon Web Services accounts where you want to run the automation. Use
-- this operation to start an automation in multiple Amazon Web Services
-- Regions and multiple Amazon Web Services accounts. For more information,
-- see
-- <https://docs.aws.amazon.com/systems-manager/latest/userguide/systems-manager-automation-multiple-accounts-and-regions.html Running Automation workflows in multiple Amazon Web Services Regions and Amazon Web Services accounts>
-- in the /Amazon Web Services Systems Manager User Guide/.
startAutomationExecution_targetLocations :: Lens.Lens' StartAutomationExecution (Prelude.Maybe (Prelude.NonEmpty TargetLocation))
startAutomationExecution_targetLocations = Lens.lens (\StartAutomationExecution' {targetLocations} -> targetLocations) (\s@StartAutomationExecution' {} a -> s {targetLocations = a} :: StartAutomationExecution) Prelude.. Lens.mapping Lens.coerced

-- | The name of the parameter used as the target resource for the
-- rate-controlled execution. Required if you specify targets.
startAutomationExecution_targetParameterName :: Lens.Lens' StartAutomationExecution (Prelude.Maybe Prelude.Text)
startAutomationExecution_targetParameterName = Lens.lens (\StartAutomationExecution' {targetParameterName} -> targetParameterName) (\s@StartAutomationExecution' {} a -> s {targetParameterName = a} :: StartAutomationExecution)

-- | A key-value mapping of document parameters to target resources. Both
-- Targets and TargetMaps can\'t be specified together.
startAutomationExecution_targetMaps :: Lens.Lens' StartAutomationExecution (Prelude.Maybe [Prelude.HashMap Prelude.Text [Prelude.Text]])
startAutomationExecution_targetMaps = Lens.lens (\StartAutomationExecution' {targetMaps} -> targetMaps) (\s@StartAutomationExecution' {} a -> s {targetMaps = a} :: StartAutomationExecution) Prelude.. Lens.mapping Lens.coerced

-- | A key-value mapping to target resources. Required if you specify
-- TargetParameterName.
startAutomationExecution_targets :: Lens.Lens' StartAutomationExecution (Prelude.Maybe [Target])
startAutomationExecution_targets = Lens.lens (\StartAutomationExecution' {targets} -> targets) (\s@StartAutomationExecution' {} a -> s {targets = a} :: StartAutomationExecution) Prelude.. Lens.mapping Lens.coerced

-- | The maximum number of targets allowed to run this task in parallel. You
-- can specify a number, such as 10, or a percentage, such as 10%. The
-- default value is @10@.
startAutomationExecution_maxConcurrency :: Lens.Lens' StartAutomationExecution (Prelude.Maybe Prelude.Text)
startAutomationExecution_maxConcurrency = Lens.lens (\StartAutomationExecution' {maxConcurrency} -> maxConcurrency) (\s@StartAutomationExecution' {} a -> s {maxConcurrency = a} :: StartAutomationExecution)

-- | The execution mode of the automation. Valid modes include the following:
-- Auto and Interactive. The default mode is Auto.
startAutomationExecution_mode :: Lens.Lens' StartAutomationExecution (Prelude.Maybe ExecutionMode)
startAutomationExecution_mode = Lens.lens (\StartAutomationExecution' {mode} -> mode) (\s@StartAutomationExecution' {} a -> s {mode = a} :: StartAutomationExecution)

-- | The number of errors that are allowed before the system stops running
-- the automation on additional targets. You can specify either an absolute
-- number of errors, for example 10, or a percentage of the target set, for
-- example 10%. If you specify 3, for example, the system stops running the
-- automation when the fourth error is received. If you specify 0, then the
-- system stops running the automation on additional targets after the
-- first error result is returned. If you run an automation on 50 resources
-- and set max-errors to 10%, then the system stops running the automation
-- on additional targets when the sixth error is received.
--
-- Executions that are already running an automation when max-errors is
-- reached are allowed to complete, but some of these executions may fail
-- as well. If you need to ensure that there won\'t be more than max-errors
-- failed executions, set max-concurrency to 1 so the executions proceed
-- one at a time.
startAutomationExecution_maxErrors :: Lens.Lens' StartAutomationExecution (Prelude.Maybe Prelude.Text)
startAutomationExecution_maxErrors = Lens.lens (\StartAutomationExecution' {maxErrors} -> maxErrors) (\s@StartAutomationExecution' {} a -> s {maxErrors = a} :: StartAutomationExecution)

-- | The version of the Automation runbook to use for this execution.
startAutomationExecution_documentVersion :: Lens.Lens' StartAutomationExecution (Prelude.Maybe Prelude.Text)
startAutomationExecution_documentVersion = Lens.lens (\StartAutomationExecution' {documentVersion} -> documentVersion) (\s@StartAutomationExecution' {} a -> s {documentVersion = a} :: StartAutomationExecution)

-- | A key-value map of execution parameters, which match the declared
-- parameters in the Automation runbook.
startAutomationExecution_parameters :: Lens.Lens' StartAutomationExecution (Prelude.Maybe (Prelude.HashMap Prelude.Text [Prelude.Text]))
startAutomationExecution_parameters = Lens.lens (\StartAutomationExecution' {parameters} -> parameters) (\s@StartAutomationExecution' {} a -> s {parameters = a} :: StartAutomationExecution) Prelude.. Lens.mapping Lens.coerced

-- | The name of the SSM document to run. This can be a public document or a
-- custom document. To run a shared document belonging to another account,
-- specify the document ARN. For more information about how to use shared
-- documents, see
-- <https://docs.aws.amazon.com/systems-manager/latest/userguide/ssm-using-shared.html Using shared SSM documents>
-- in the /Amazon Web Services Systems Manager User Guide/.
startAutomationExecution_documentName :: Lens.Lens' StartAutomationExecution Prelude.Text
startAutomationExecution_documentName = Lens.lens (\StartAutomationExecution' {documentName} -> documentName) (\s@StartAutomationExecution' {} a -> s {documentName = a} :: StartAutomationExecution)

instance Core.AWSRequest StartAutomationExecution where
  type
    AWSResponse StartAutomationExecution =
      StartAutomationExecutionResponse
  request = Request.postJSON defaultService
  response =
    Response.receiveJSON
      ( \s h x ->
          StartAutomationExecutionResponse'
            Prelude.<$> (x Core..?> "AutomationExecutionId")
            Prelude.<*> (Prelude.pure (Prelude.fromEnum s))
      )

instance Prelude.Hashable StartAutomationExecution where
  hashWithSalt _salt StartAutomationExecution' {..} =
    _salt `Prelude.hashWithSalt` tags
      `Prelude.hashWithSalt` clientToken
      `Prelude.hashWithSalt` targetLocations
      `Prelude.hashWithSalt` targetParameterName
      `Prelude.hashWithSalt` targetMaps
      `Prelude.hashWithSalt` targets
      `Prelude.hashWithSalt` maxConcurrency
      `Prelude.hashWithSalt` mode
      `Prelude.hashWithSalt` maxErrors
      `Prelude.hashWithSalt` documentVersion
      `Prelude.hashWithSalt` parameters
      `Prelude.hashWithSalt` documentName

instance Prelude.NFData StartAutomationExecution where
  rnf StartAutomationExecution' {..} =
    Prelude.rnf tags
      `Prelude.seq` Prelude.rnf clientToken
      `Prelude.seq` Prelude.rnf targetLocations
      `Prelude.seq` Prelude.rnf targetParameterName
      `Prelude.seq` Prelude.rnf targetMaps
      `Prelude.seq` Prelude.rnf targets
      `Prelude.seq` Prelude.rnf maxConcurrency
      `Prelude.seq` Prelude.rnf mode
      `Prelude.seq` Prelude.rnf maxErrors
      `Prelude.seq` Prelude.rnf documentVersion
      `Prelude.seq` Prelude.rnf parameters
      `Prelude.seq` Prelude.rnf documentName

instance Core.ToHeaders StartAutomationExecution where
  toHeaders =
    Prelude.const
      ( Prelude.mconcat
          [ "X-Amz-Target"
              Core.=# ( "AmazonSSM.StartAutomationExecution" ::
                          Prelude.ByteString
                      ),
            "Content-Type"
              Core.=# ( "application/x-amz-json-1.1" ::
                          Prelude.ByteString
                      )
          ]
      )

instance Core.ToJSON StartAutomationExecution where
  toJSON StartAutomationExecution' {..} =
    Core.object
      ( Prelude.catMaybes
          [ ("Tags" Core..=) Prelude.<$> tags,
            ("ClientToken" Core..=) Prelude.<$> clientToken,
            ("TargetLocations" Core..=)
              Prelude.<$> targetLocations,
            ("TargetParameterName" Core..=)
              Prelude.<$> targetParameterName,
            ("TargetMaps" Core..=) Prelude.<$> targetMaps,
            ("Targets" Core..=) Prelude.<$> targets,
            ("MaxConcurrency" Core..=)
              Prelude.<$> maxConcurrency,
            ("Mode" Core..=) Prelude.<$> mode,
            ("MaxErrors" Core..=) Prelude.<$> maxErrors,
            ("DocumentVersion" Core..=)
              Prelude.<$> documentVersion,
            ("Parameters" Core..=) Prelude.<$> parameters,
            Prelude.Just ("DocumentName" Core..= documentName)
          ]
      )

instance Core.ToPath StartAutomationExecution where
  toPath = Prelude.const "/"

instance Core.ToQuery StartAutomationExecution where
  toQuery = Prelude.const Prelude.mempty

-- | /See:/ 'newStartAutomationExecutionResponse' smart constructor.
data StartAutomationExecutionResponse = StartAutomationExecutionResponse'
  { -- | The unique ID of a newly scheduled automation execution.
    automationExecutionId :: Prelude.Maybe Prelude.Text,
    -- | The response's http status code.
    httpStatus :: Prelude.Int
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'StartAutomationExecutionResponse' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'automationExecutionId', 'startAutomationExecutionResponse_automationExecutionId' - The unique ID of a newly scheduled automation execution.
--
-- 'httpStatus', 'startAutomationExecutionResponse_httpStatus' - The response's http status code.
newStartAutomationExecutionResponse ::
  -- | 'httpStatus'
  Prelude.Int ->
  StartAutomationExecutionResponse
newStartAutomationExecutionResponse pHttpStatus_ =
  StartAutomationExecutionResponse'
    { automationExecutionId =
        Prelude.Nothing,
      httpStatus = pHttpStatus_
    }

-- | The unique ID of a newly scheduled automation execution.
startAutomationExecutionResponse_automationExecutionId :: Lens.Lens' StartAutomationExecutionResponse (Prelude.Maybe Prelude.Text)
startAutomationExecutionResponse_automationExecutionId = Lens.lens (\StartAutomationExecutionResponse' {automationExecutionId} -> automationExecutionId) (\s@StartAutomationExecutionResponse' {} a -> s {automationExecutionId = a} :: StartAutomationExecutionResponse)

-- | The response's http status code.
startAutomationExecutionResponse_httpStatus :: Lens.Lens' StartAutomationExecutionResponse Prelude.Int
startAutomationExecutionResponse_httpStatus = Lens.lens (\StartAutomationExecutionResponse' {httpStatus} -> httpStatus) (\s@StartAutomationExecutionResponse' {} a -> s {httpStatus = a} :: StartAutomationExecutionResponse)

instance
  Prelude.NFData
    StartAutomationExecutionResponse
  where
  rnf StartAutomationExecutionResponse' {..} =
    Prelude.rnf automationExecutionId
      `Prelude.seq` Prelude.rnf httpStatus
