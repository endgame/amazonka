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
-- Module      : Amazonka.OpsWorks.CreateDeployment
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
--
-- Runs deployment or stack commands. For more information, see
-- <https://docs.aws.amazon.com/opsworks/latest/userguide/workingapps-deploying.html Deploying Apps>
-- and
-- <https://docs.aws.amazon.com/opsworks/latest/userguide/workingstacks-commands.html Run Stack Commands>.
--
-- __Required Permissions__: To use this action, an IAM user must have a
-- Deploy or Manage permissions level for the stack, or an attached policy
-- that explicitly grants permissions. For more information on user
-- permissions, see
-- <https://docs.aws.amazon.com/opsworks/latest/userguide/opsworks-security-users.html Managing User Permissions>.
module Amazonka.OpsWorks.CreateDeployment
  ( -- * Creating a Request
    CreateDeployment (..),
    newCreateDeployment,

    -- * Request Lenses
    createDeployment_customJson,
    createDeployment_comment,
    createDeployment_layerIds,
    createDeployment_instanceIds,
    createDeployment_appId,
    createDeployment_stackId,
    createDeployment_command,

    -- * Destructuring the Response
    CreateDeploymentResponse (..),
    newCreateDeploymentResponse,

    -- * Response Lenses
    createDeploymentResponse_deploymentId,
    createDeploymentResponse_httpStatus,
  )
where

import qualified Amazonka.Core as Core
import qualified Amazonka.Lens as Lens
import Amazonka.OpsWorks.Types
import qualified Amazonka.Prelude as Prelude
import qualified Amazonka.Request as Request
import qualified Amazonka.Response as Response

-- | /See:/ 'newCreateDeployment' smart constructor.
data CreateDeployment = CreateDeployment'
  { -- | A string that contains user-defined, custom JSON. You can use this
    -- parameter to override some corresponding default stack configuration
    -- JSON values. The string should be in the following format:
    --
    -- @\"{\\\"key1\\\": \\\"value1\\\", \\\"key2\\\": \\\"value2\\\",...}\"@
    --
    -- For more information about custom JSON, see
    -- <https://docs.aws.amazon.com/opsworks/latest/userguide/workingstacks-json.html Use Custom JSON to Modify the Stack Configuration Attributes>
    -- and
    -- <https://docs.aws.amazon.com/opsworks/latest/userguide/workingcookbook-json-override.html Overriding Attributes With Custom JSON>.
    customJson :: Prelude.Maybe Prelude.Text,
    -- | A user-defined comment.
    comment :: Prelude.Maybe Prelude.Text,
    -- | The layer IDs for the deployment targets.
    layerIds :: Prelude.Maybe [Prelude.Text],
    -- | The instance IDs for the deployment targets.
    instanceIds :: Prelude.Maybe [Prelude.Text],
    -- | The app ID. This parameter is required for app deployments, but not for
    -- other deployment commands.
    appId :: Prelude.Maybe Prelude.Text,
    -- | The stack ID.
    stackId :: Prelude.Text,
    -- | A @DeploymentCommand@ object that specifies the deployment command and
    -- any associated arguments.
    command :: DeploymentCommand
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'CreateDeployment' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'customJson', 'createDeployment_customJson' - A string that contains user-defined, custom JSON. You can use this
-- parameter to override some corresponding default stack configuration
-- JSON values. The string should be in the following format:
--
-- @\"{\\\"key1\\\": \\\"value1\\\", \\\"key2\\\": \\\"value2\\\",...}\"@
--
-- For more information about custom JSON, see
-- <https://docs.aws.amazon.com/opsworks/latest/userguide/workingstacks-json.html Use Custom JSON to Modify the Stack Configuration Attributes>
-- and
-- <https://docs.aws.amazon.com/opsworks/latest/userguide/workingcookbook-json-override.html Overriding Attributes With Custom JSON>.
--
-- 'comment', 'createDeployment_comment' - A user-defined comment.
--
-- 'layerIds', 'createDeployment_layerIds' - The layer IDs for the deployment targets.
--
-- 'instanceIds', 'createDeployment_instanceIds' - The instance IDs for the deployment targets.
--
-- 'appId', 'createDeployment_appId' - The app ID. This parameter is required for app deployments, but not for
-- other deployment commands.
--
-- 'stackId', 'createDeployment_stackId' - The stack ID.
--
-- 'command', 'createDeployment_command' - A @DeploymentCommand@ object that specifies the deployment command and
-- any associated arguments.
newCreateDeployment ::
  -- | 'stackId'
  Prelude.Text ->
  -- | 'command'
  DeploymentCommand ->
  CreateDeployment
newCreateDeployment pStackId_ pCommand_ =
  CreateDeployment'
    { customJson = Prelude.Nothing,
      comment = Prelude.Nothing,
      layerIds = Prelude.Nothing,
      instanceIds = Prelude.Nothing,
      appId = Prelude.Nothing,
      stackId = pStackId_,
      command = pCommand_
    }

-- | A string that contains user-defined, custom JSON. You can use this
-- parameter to override some corresponding default stack configuration
-- JSON values. The string should be in the following format:
--
-- @\"{\\\"key1\\\": \\\"value1\\\", \\\"key2\\\": \\\"value2\\\",...}\"@
--
-- For more information about custom JSON, see
-- <https://docs.aws.amazon.com/opsworks/latest/userguide/workingstacks-json.html Use Custom JSON to Modify the Stack Configuration Attributes>
-- and
-- <https://docs.aws.amazon.com/opsworks/latest/userguide/workingcookbook-json-override.html Overriding Attributes With Custom JSON>.
createDeployment_customJson :: Lens.Lens' CreateDeployment (Prelude.Maybe Prelude.Text)
createDeployment_customJson = Lens.lens (\CreateDeployment' {customJson} -> customJson) (\s@CreateDeployment' {} a -> s {customJson = a} :: CreateDeployment)

-- | A user-defined comment.
createDeployment_comment :: Lens.Lens' CreateDeployment (Prelude.Maybe Prelude.Text)
createDeployment_comment = Lens.lens (\CreateDeployment' {comment} -> comment) (\s@CreateDeployment' {} a -> s {comment = a} :: CreateDeployment)

-- | The layer IDs for the deployment targets.
createDeployment_layerIds :: Lens.Lens' CreateDeployment (Prelude.Maybe [Prelude.Text])
createDeployment_layerIds = Lens.lens (\CreateDeployment' {layerIds} -> layerIds) (\s@CreateDeployment' {} a -> s {layerIds = a} :: CreateDeployment) Prelude.. Lens.mapping Lens.coerced

-- | The instance IDs for the deployment targets.
createDeployment_instanceIds :: Lens.Lens' CreateDeployment (Prelude.Maybe [Prelude.Text])
createDeployment_instanceIds = Lens.lens (\CreateDeployment' {instanceIds} -> instanceIds) (\s@CreateDeployment' {} a -> s {instanceIds = a} :: CreateDeployment) Prelude.. Lens.mapping Lens.coerced

-- | The app ID. This parameter is required for app deployments, but not for
-- other deployment commands.
createDeployment_appId :: Lens.Lens' CreateDeployment (Prelude.Maybe Prelude.Text)
createDeployment_appId = Lens.lens (\CreateDeployment' {appId} -> appId) (\s@CreateDeployment' {} a -> s {appId = a} :: CreateDeployment)

-- | The stack ID.
createDeployment_stackId :: Lens.Lens' CreateDeployment Prelude.Text
createDeployment_stackId = Lens.lens (\CreateDeployment' {stackId} -> stackId) (\s@CreateDeployment' {} a -> s {stackId = a} :: CreateDeployment)

-- | A @DeploymentCommand@ object that specifies the deployment command and
-- any associated arguments.
createDeployment_command :: Lens.Lens' CreateDeployment DeploymentCommand
createDeployment_command = Lens.lens (\CreateDeployment' {command} -> command) (\s@CreateDeployment' {} a -> s {command = a} :: CreateDeployment)

instance Core.AWSRequest CreateDeployment where
  type
    AWSResponse CreateDeployment =
      CreateDeploymentResponse
  request = Request.postJSON defaultService
  response =
    Response.receiveJSON
      ( \s h x ->
          CreateDeploymentResponse'
            Prelude.<$> (x Core..?> "DeploymentId")
            Prelude.<*> (Prelude.pure (Prelude.fromEnum s))
      )

instance Prelude.Hashable CreateDeployment where
  hashWithSalt _salt CreateDeployment' {..} =
    _salt `Prelude.hashWithSalt` customJson
      `Prelude.hashWithSalt` comment
      `Prelude.hashWithSalt` layerIds
      `Prelude.hashWithSalt` instanceIds
      `Prelude.hashWithSalt` appId
      `Prelude.hashWithSalt` stackId
      `Prelude.hashWithSalt` command

instance Prelude.NFData CreateDeployment where
  rnf CreateDeployment' {..} =
    Prelude.rnf customJson
      `Prelude.seq` Prelude.rnf comment
      `Prelude.seq` Prelude.rnf layerIds
      `Prelude.seq` Prelude.rnf instanceIds
      `Prelude.seq` Prelude.rnf appId
      `Prelude.seq` Prelude.rnf stackId
      `Prelude.seq` Prelude.rnf command

instance Core.ToHeaders CreateDeployment where
  toHeaders =
    Prelude.const
      ( Prelude.mconcat
          [ "X-Amz-Target"
              Core.=# ( "OpsWorks_20130218.CreateDeployment" ::
                          Prelude.ByteString
                      ),
            "Content-Type"
              Core.=# ( "application/x-amz-json-1.1" ::
                          Prelude.ByteString
                      )
          ]
      )

instance Core.ToJSON CreateDeployment where
  toJSON CreateDeployment' {..} =
    Core.object
      ( Prelude.catMaybes
          [ ("CustomJson" Core..=) Prelude.<$> customJson,
            ("Comment" Core..=) Prelude.<$> comment,
            ("LayerIds" Core..=) Prelude.<$> layerIds,
            ("InstanceIds" Core..=) Prelude.<$> instanceIds,
            ("AppId" Core..=) Prelude.<$> appId,
            Prelude.Just ("StackId" Core..= stackId),
            Prelude.Just ("Command" Core..= command)
          ]
      )

instance Core.ToPath CreateDeployment where
  toPath = Prelude.const "/"

instance Core.ToQuery CreateDeployment where
  toQuery = Prelude.const Prelude.mempty

-- | Contains the response to a @CreateDeployment@ request.
--
-- /See:/ 'newCreateDeploymentResponse' smart constructor.
data CreateDeploymentResponse = CreateDeploymentResponse'
  { -- | The deployment ID, which can be used with other requests to identify the
    -- deployment.
    deploymentId :: Prelude.Maybe Prelude.Text,
    -- | The response's http status code.
    httpStatus :: Prelude.Int
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'CreateDeploymentResponse' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'deploymentId', 'createDeploymentResponse_deploymentId' - The deployment ID, which can be used with other requests to identify the
-- deployment.
--
-- 'httpStatus', 'createDeploymentResponse_httpStatus' - The response's http status code.
newCreateDeploymentResponse ::
  -- | 'httpStatus'
  Prelude.Int ->
  CreateDeploymentResponse
newCreateDeploymentResponse pHttpStatus_ =
  CreateDeploymentResponse'
    { deploymentId =
        Prelude.Nothing,
      httpStatus = pHttpStatus_
    }

-- | The deployment ID, which can be used with other requests to identify the
-- deployment.
createDeploymentResponse_deploymentId :: Lens.Lens' CreateDeploymentResponse (Prelude.Maybe Prelude.Text)
createDeploymentResponse_deploymentId = Lens.lens (\CreateDeploymentResponse' {deploymentId} -> deploymentId) (\s@CreateDeploymentResponse' {} a -> s {deploymentId = a} :: CreateDeploymentResponse)

-- | The response's http status code.
createDeploymentResponse_httpStatus :: Lens.Lens' CreateDeploymentResponse Prelude.Int
createDeploymentResponse_httpStatus = Lens.lens (\CreateDeploymentResponse' {httpStatus} -> httpStatus) (\s@CreateDeploymentResponse' {} a -> s {httpStatus = a} :: CreateDeploymentResponse)

instance Prelude.NFData CreateDeploymentResponse where
  rnf CreateDeploymentResponse' {..} =
    Prelude.rnf deploymentId
      `Prelude.seq` Prelude.rnf httpStatus
