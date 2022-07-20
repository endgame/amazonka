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
-- Module      : Amazonka.CloudFormation.PublishType
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
--
-- Publishes the specified extension to the CloudFormation registry as a
-- public extension in this region. Public extensions are available for use
-- by all CloudFormation users. For more information on publishing
-- extensions, see
-- <https://docs.aws.amazon.com/cloudformation-cli/latest/userguide/publish-extension.html Publishing extensions to make them available for public use>
-- in the /CloudFormation CLI User Guide/.
--
-- To publish an extension, you must be registered as a publisher with
-- CloudFormation. For more information, see
-- <https://docs.aws.amazon.com/AWSCloudFormation/latest/APIReference/API_RegisterPublisher.html RegisterPublisher>.
module Amazonka.CloudFormation.PublishType
  ( -- * Creating a Request
    PublishType (..),
    newPublishType,

    -- * Request Lenses
    publishType_type,
    publishType_arn,
    publishType_publicVersionNumber,
    publishType_typeName,

    -- * Destructuring the Response
    PublishTypeResponse (..),
    newPublishTypeResponse,

    -- * Response Lenses
    publishTypeResponse_publicTypeArn,
    publishTypeResponse_httpStatus,
  )
where

import Amazonka.CloudFormation.Types
import qualified Amazonka.Core as Core
import qualified Amazonka.Lens as Lens
import qualified Amazonka.Prelude as Prelude
import qualified Amazonka.Request as Request
import qualified Amazonka.Response as Response

-- | /See:/ 'newPublishType' smart constructor.
data PublishType = PublishType'
  { -- | The type of the extension.
    --
    -- Conditional: You must specify @Arn@, or @TypeName@ and @Type@.
    type' :: Prelude.Maybe ThirdPartyType,
    -- | The Amazon Resource Number (ARN) of the extension.
    --
    -- Conditional: You must specify @Arn@, or @TypeName@ and @Type@.
    arn :: Prelude.Maybe Prelude.Text,
    -- | The version number to assign to this version of the extension.
    --
    -- Use the following format, and adhere to semantic versioning when
    -- assigning a version number to your extension:
    --
    -- @MAJOR.MINOR.PATCH@
    --
    -- For more information, see
    -- <https://semver.org/ Semantic Versioning 2.0.0>.
    --
    -- If you do not specify a version number, CloudFormation increments the
    -- version number by one minor version release.
    --
    -- The first time you publish a type, CloudFormation sets the version
    -- number to @1.0.0@, regardless of the value you specify.
    publicVersionNumber :: Prelude.Maybe Prelude.Text,
    -- | The name of the extension.
    --
    -- Conditional: You must specify @Arn@, or @TypeName@ and @Type@.
    typeName :: Prelude.Maybe Prelude.Text
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'PublishType' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'type'', 'publishType_type' - The type of the extension.
--
-- Conditional: You must specify @Arn@, or @TypeName@ and @Type@.
--
-- 'arn', 'publishType_arn' - The Amazon Resource Number (ARN) of the extension.
--
-- Conditional: You must specify @Arn@, or @TypeName@ and @Type@.
--
-- 'publicVersionNumber', 'publishType_publicVersionNumber' - The version number to assign to this version of the extension.
--
-- Use the following format, and adhere to semantic versioning when
-- assigning a version number to your extension:
--
-- @MAJOR.MINOR.PATCH@
--
-- For more information, see
-- <https://semver.org/ Semantic Versioning 2.0.0>.
--
-- If you do not specify a version number, CloudFormation increments the
-- version number by one minor version release.
--
-- The first time you publish a type, CloudFormation sets the version
-- number to @1.0.0@, regardless of the value you specify.
--
-- 'typeName', 'publishType_typeName' - The name of the extension.
--
-- Conditional: You must specify @Arn@, or @TypeName@ and @Type@.
newPublishType ::
  PublishType
newPublishType =
  PublishType'
    { type' = Prelude.Nothing,
      arn = Prelude.Nothing,
      publicVersionNumber = Prelude.Nothing,
      typeName = Prelude.Nothing
    }

-- | The type of the extension.
--
-- Conditional: You must specify @Arn@, or @TypeName@ and @Type@.
publishType_type :: Lens.Lens' PublishType (Prelude.Maybe ThirdPartyType)
publishType_type = Lens.lens (\PublishType' {type'} -> type') (\s@PublishType' {} a -> s {type' = a} :: PublishType)

-- | The Amazon Resource Number (ARN) of the extension.
--
-- Conditional: You must specify @Arn@, or @TypeName@ and @Type@.
publishType_arn :: Lens.Lens' PublishType (Prelude.Maybe Prelude.Text)
publishType_arn = Lens.lens (\PublishType' {arn} -> arn) (\s@PublishType' {} a -> s {arn = a} :: PublishType)

-- | The version number to assign to this version of the extension.
--
-- Use the following format, and adhere to semantic versioning when
-- assigning a version number to your extension:
--
-- @MAJOR.MINOR.PATCH@
--
-- For more information, see
-- <https://semver.org/ Semantic Versioning 2.0.0>.
--
-- If you do not specify a version number, CloudFormation increments the
-- version number by one minor version release.
--
-- The first time you publish a type, CloudFormation sets the version
-- number to @1.0.0@, regardless of the value you specify.
publishType_publicVersionNumber :: Lens.Lens' PublishType (Prelude.Maybe Prelude.Text)
publishType_publicVersionNumber = Lens.lens (\PublishType' {publicVersionNumber} -> publicVersionNumber) (\s@PublishType' {} a -> s {publicVersionNumber = a} :: PublishType)

-- | The name of the extension.
--
-- Conditional: You must specify @Arn@, or @TypeName@ and @Type@.
publishType_typeName :: Lens.Lens' PublishType (Prelude.Maybe Prelude.Text)
publishType_typeName = Lens.lens (\PublishType' {typeName} -> typeName) (\s@PublishType' {} a -> s {typeName = a} :: PublishType)

instance Core.AWSRequest PublishType where
  type AWSResponse PublishType = PublishTypeResponse
  request = Request.postQuery defaultService
  response =
    Response.receiveXMLWrapper
      "PublishTypeResult"
      ( \s h x ->
          PublishTypeResponse'
            Prelude.<$> (x Core..@? "PublicTypeArn")
            Prelude.<*> (Prelude.pure (Prelude.fromEnum s))
      )

instance Prelude.Hashable PublishType where
  hashWithSalt _salt PublishType' {..} =
    _salt `Prelude.hashWithSalt` type'
      `Prelude.hashWithSalt` arn
      `Prelude.hashWithSalt` publicVersionNumber
      `Prelude.hashWithSalt` typeName

instance Prelude.NFData PublishType where
  rnf PublishType' {..} =
    Prelude.rnf type'
      `Prelude.seq` Prelude.rnf arn
      `Prelude.seq` Prelude.rnf publicVersionNumber
      `Prelude.seq` Prelude.rnf typeName

instance Core.ToHeaders PublishType where
  toHeaders = Prelude.const Prelude.mempty

instance Core.ToPath PublishType where
  toPath = Prelude.const "/"

instance Core.ToQuery PublishType where
  toQuery PublishType' {..} =
    Prelude.mconcat
      [ "Action"
          Core.=: ("PublishType" :: Prelude.ByteString),
        "Version"
          Core.=: ("2010-05-15" :: Prelude.ByteString),
        "Type" Core.=: type',
        "Arn" Core.=: arn,
        "PublicVersionNumber" Core.=: publicVersionNumber,
        "TypeName" Core.=: typeName
      ]

-- | /See:/ 'newPublishTypeResponse' smart constructor.
data PublishTypeResponse = PublishTypeResponse'
  { -- | The Amazon Resource Number (ARN) assigned to the public extension upon
    -- publication.
    publicTypeArn :: Prelude.Maybe Prelude.Text,
    -- | The response's http status code.
    httpStatus :: Prelude.Int
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'PublishTypeResponse' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'publicTypeArn', 'publishTypeResponse_publicTypeArn' - The Amazon Resource Number (ARN) assigned to the public extension upon
-- publication.
--
-- 'httpStatus', 'publishTypeResponse_httpStatus' - The response's http status code.
newPublishTypeResponse ::
  -- | 'httpStatus'
  Prelude.Int ->
  PublishTypeResponse
newPublishTypeResponse pHttpStatus_ =
  PublishTypeResponse'
    { publicTypeArn =
        Prelude.Nothing,
      httpStatus = pHttpStatus_
    }

-- | The Amazon Resource Number (ARN) assigned to the public extension upon
-- publication.
publishTypeResponse_publicTypeArn :: Lens.Lens' PublishTypeResponse (Prelude.Maybe Prelude.Text)
publishTypeResponse_publicTypeArn = Lens.lens (\PublishTypeResponse' {publicTypeArn} -> publicTypeArn) (\s@PublishTypeResponse' {} a -> s {publicTypeArn = a} :: PublishTypeResponse)

-- | The response's http status code.
publishTypeResponse_httpStatus :: Lens.Lens' PublishTypeResponse Prelude.Int
publishTypeResponse_httpStatus = Lens.lens (\PublishTypeResponse' {httpStatus} -> httpStatus) (\s@PublishTypeResponse' {} a -> s {httpStatus = a} :: PublishTypeResponse)

instance Prelude.NFData PublishTypeResponse where
  rnf PublishTypeResponse' {..} =
    Prelude.rnf publicTypeArn
      `Prelude.seq` Prelude.rnf httpStatus
