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
-- Module      : Amazonka.GuardDuty.CreateThreatIntelSet
-- Copyright   : (c) 2013-2023 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
--
-- Creates a new ThreatIntelSet. ThreatIntelSets consist of known malicious
-- IP addresses. GuardDuty generates findings based on ThreatIntelSets.
-- Only users of the administrator account can use this operation.
module Amazonka.GuardDuty.CreateThreatIntelSet
  ( -- * Creating a Request
    CreateThreatIntelSet (..),
    newCreateThreatIntelSet,

    -- * Request Lenses
    createThreatIntelSet_clientToken,
    createThreatIntelSet_tags,
    createThreatIntelSet_detectorId,
    createThreatIntelSet_name,
    createThreatIntelSet_format,
    createThreatIntelSet_location,
    createThreatIntelSet_activate,

    -- * Destructuring the Response
    CreateThreatIntelSetResponse (..),
    newCreateThreatIntelSetResponse,

    -- * Response Lenses
    createThreatIntelSetResponse_httpStatus,
    createThreatIntelSetResponse_threatIntelSetId,
  )
where

import qualified Amazonka.Core as Core
import qualified Amazonka.Core.Lens.Internal as Lens
import qualified Amazonka.Data as Data
import Amazonka.GuardDuty.Types
import qualified Amazonka.Prelude as Prelude
import qualified Amazonka.Request as Request
import qualified Amazonka.Response as Response

-- | /See:/ 'newCreateThreatIntelSet' smart constructor.
data CreateThreatIntelSet = CreateThreatIntelSet'
  { -- | The idempotency token for the create request.
    clientToken :: Prelude.Maybe Prelude.Text,
    -- | The tags to be added to a new threat list resource.
    tags :: Prelude.Maybe (Prelude.HashMap Prelude.Text Prelude.Text),
    -- | The unique ID of the detector of the GuardDuty account that you want to
    -- create a threatIntelSet for.
    detectorId :: Prelude.Text,
    -- | A user-friendly ThreatIntelSet name displayed in all findings that are
    -- generated by activity that involves IP addresses included in this
    -- ThreatIntelSet.
    name :: Prelude.Text,
    -- | The format of the file that contains the ThreatIntelSet.
    format :: ThreatIntelSetFormat,
    -- | The URI of the file that contains the ThreatIntelSet.
    location :: Prelude.Text,
    -- | A Boolean value that indicates whether GuardDuty is to start using the
    -- uploaded ThreatIntelSet.
    activate :: Prelude.Bool
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'CreateThreatIntelSet' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'clientToken', 'createThreatIntelSet_clientToken' - The idempotency token for the create request.
--
-- 'tags', 'createThreatIntelSet_tags' - The tags to be added to a new threat list resource.
--
-- 'detectorId', 'createThreatIntelSet_detectorId' - The unique ID of the detector of the GuardDuty account that you want to
-- create a threatIntelSet for.
--
-- 'name', 'createThreatIntelSet_name' - A user-friendly ThreatIntelSet name displayed in all findings that are
-- generated by activity that involves IP addresses included in this
-- ThreatIntelSet.
--
-- 'format', 'createThreatIntelSet_format' - The format of the file that contains the ThreatIntelSet.
--
-- 'location', 'createThreatIntelSet_location' - The URI of the file that contains the ThreatIntelSet.
--
-- 'activate', 'createThreatIntelSet_activate' - A Boolean value that indicates whether GuardDuty is to start using the
-- uploaded ThreatIntelSet.
newCreateThreatIntelSet ::
  -- | 'detectorId'
  Prelude.Text ->
  -- | 'name'
  Prelude.Text ->
  -- | 'format'
  ThreatIntelSetFormat ->
  -- | 'location'
  Prelude.Text ->
  -- | 'activate'
  Prelude.Bool ->
  CreateThreatIntelSet
newCreateThreatIntelSet
  pDetectorId_
  pName_
  pFormat_
  pLocation_
  pActivate_ =
    CreateThreatIntelSet'
      { clientToken =
          Prelude.Nothing,
        tags = Prelude.Nothing,
        detectorId = pDetectorId_,
        name = pName_,
        format = pFormat_,
        location = pLocation_,
        activate = pActivate_
      }

-- | The idempotency token for the create request.
createThreatIntelSet_clientToken :: Lens.Lens' CreateThreatIntelSet (Prelude.Maybe Prelude.Text)
createThreatIntelSet_clientToken = Lens.lens (\CreateThreatIntelSet' {clientToken} -> clientToken) (\s@CreateThreatIntelSet' {} a -> s {clientToken = a} :: CreateThreatIntelSet)

-- | The tags to be added to a new threat list resource.
createThreatIntelSet_tags :: Lens.Lens' CreateThreatIntelSet (Prelude.Maybe (Prelude.HashMap Prelude.Text Prelude.Text))
createThreatIntelSet_tags = Lens.lens (\CreateThreatIntelSet' {tags} -> tags) (\s@CreateThreatIntelSet' {} a -> s {tags = a} :: CreateThreatIntelSet) Prelude.. Lens.mapping Lens.coerced

-- | The unique ID of the detector of the GuardDuty account that you want to
-- create a threatIntelSet for.
createThreatIntelSet_detectorId :: Lens.Lens' CreateThreatIntelSet Prelude.Text
createThreatIntelSet_detectorId = Lens.lens (\CreateThreatIntelSet' {detectorId} -> detectorId) (\s@CreateThreatIntelSet' {} a -> s {detectorId = a} :: CreateThreatIntelSet)

-- | A user-friendly ThreatIntelSet name displayed in all findings that are
-- generated by activity that involves IP addresses included in this
-- ThreatIntelSet.
createThreatIntelSet_name :: Lens.Lens' CreateThreatIntelSet Prelude.Text
createThreatIntelSet_name = Lens.lens (\CreateThreatIntelSet' {name} -> name) (\s@CreateThreatIntelSet' {} a -> s {name = a} :: CreateThreatIntelSet)

-- | The format of the file that contains the ThreatIntelSet.
createThreatIntelSet_format :: Lens.Lens' CreateThreatIntelSet ThreatIntelSetFormat
createThreatIntelSet_format = Lens.lens (\CreateThreatIntelSet' {format} -> format) (\s@CreateThreatIntelSet' {} a -> s {format = a} :: CreateThreatIntelSet)

-- | The URI of the file that contains the ThreatIntelSet.
createThreatIntelSet_location :: Lens.Lens' CreateThreatIntelSet Prelude.Text
createThreatIntelSet_location = Lens.lens (\CreateThreatIntelSet' {location} -> location) (\s@CreateThreatIntelSet' {} a -> s {location = a} :: CreateThreatIntelSet)

-- | A Boolean value that indicates whether GuardDuty is to start using the
-- uploaded ThreatIntelSet.
createThreatIntelSet_activate :: Lens.Lens' CreateThreatIntelSet Prelude.Bool
createThreatIntelSet_activate = Lens.lens (\CreateThreatIntelSet' {activate} -> activate) (\s@CreateThreatIntelSet' {} a -> s {activate = a} :: CreateThreatIntelSet)

instance Core.AWSRequest CreateThreatIntelSet where
  type
    AWSResponse CreateThreatIntelSet =
      CreateThreatIntelSetResponse
  request overrides =
    Request.postJSON (overrides defaultService)
  response =
    Response.receiveJSON
      ( \s h x ->
          CreateThreatIntelSetResponse'
            Prelude.<$> (Prelude.pure (Prelude.fromEnum s))
            Prelude.<*> (x Data..:> "threatIntelSetId")
      )

instance Prelude.Hashable CreateThreatIntelSet where
  hashWithSalt _salt CreateThreatIntelSet' {..} =
    _salt
      `Prelude.hashWithSalt` clientToken
      `Prelude.hashWithSalt` tags
      `Prelude.hashWithSalt` detectorId
      `Prelude.hashWithSalt` name
      `Prelude.hashWithSalt` format
      `Prelude.hashWithSalt` location
      `Prelude.hashWithSalt` activate

instance Prelude.NFData CreateThreatIntelSet where
  rnf CreateThreatIntelSet' {..} =
    Prelude.rnf clientToken `Prelude.seq`
      Prelude.rnf tags `Prelude.seq`
        Prelude.rnf detectorId `Prelude.seq`
          Prelude.rnf name `Prelude.seq`
            Prelude.rnf format `Prelude.seq`
              Prelude.rnf location `Prelude.seq`
                Prelude.rnf activate

instance Data.ToHeaders CreateThreatIntelSet where
  toHeaders =
    Prelude.const
      ( Prelude.mconcat
          [ "Content-Type"
              Data.=# ( "application/x-amz-json-1.1" ::
                          Prelude.ByteString
                      )
          ]
      )

instance Data.ToJSON CreateThreatIntelSet where
  toJSON CreateThreatIntelSet' {..} =
    Data.object
      ( Prelude.catMaybes
          [ ("clientToken" Data..=) Prelude.<$> clientToken,
            ("tags" Data..=) Prelude.<$> tags,
            Prelude.Just ("name" Data..= name),
            Prelude.Just ("format" Data..= format),
            Prelude.Just ("location" Data..= location),
            Prelude.Just ("activate" Data..= activate)
          ]
      )

instance Data.ToPath CreateThreatIntelSet where
  toPath CreateThreatIntelSet' {..} =
    Prelude.mconcat
      [ "/detector/",
        Data.toBS detectorId,
        "/threatintelset"
      ]

instance Data.ToQuery CreateThreatIntelSet where
  toQuery = Prelude.const Prelude.mempty

-- | /See:/ 'newCreateThreatIntelSetResponse' smart constructor.
data CreateThreatIntelSetResponse = CreateThreatIntelSetResponse'
  { -- | The response's http status code.
    httpStatus :: Prelude.Int,
    -- | The ID of the ThreatIntelSet resource.
    threatIntelSetId :: Prelude.Text
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'CreateThreatIntelSetResponse' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'httpStatus', 'createThreatIntelSetResponse_httpStatus' - The response's http status code.
--
-- 'threatIntelSetId', 'createThreatIntelSetResponse_threatIntelSetId' - The ID of the ThreatIntelSet resource.
newCreateThreatIntelSetResponse ::
  -- | 'httpStatus'
  Prelude.Int ->
  -- | 'threatIntelSetId'
  Prelude.Text ->
  CreateThreatIntelSetResponse
newCreateThreatIntelSetResponse
  pHttpStatus_
  pThreatIntelSetId_ =
    CreateThreatIntelSetResponse'
      { httpStatus =
          pHttpStatus_,
        threatIntelSetId = pThreatIntelSetId_
      }

-- | The response's http status code.
createThreatIntelSetResponse_httpStatus :: Lens.Lens' CreateThreatIntelSetResponse Prelude.Int
createThreatIntelSetResponse_httpStatus = Lens.lens (\CreateThreatIntelSetResponse' {httpStatus} -> httpStatus) (\s@CreateThreatIntelSetResponse' {} a -> s {httpStatus = a} :: CreateThreatIntelSetResponse)

-- | The ID of the ThreatIntelSet resource.
createThreatIntelSetResponse_threatIntelSetId :: Lens.Lens' CreateThreatIntelSetResponse Prelude.Text
createThreatIntelSetResponse_threatIntelSetId = Lens.lens (\CreateThreatIntelSetResponse' {threatIntelSetId} -> threatIntelSetId) (\s@CreateThreatIntelSetResponse' {} a -> s {threatIntelSetId = a} :: CreateThreatIntelSetResponse)

instance Prelude.NFData CreateThreatIntelSetResponse where
  rnf CreateThreatIntelSetResponse' {..} =
    Prelude.rnf httpStatus `Prelude.seq`
      Prelude.rnf threatIntelSetId
