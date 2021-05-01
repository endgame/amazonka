{-# LANGUAGE DeriveDataTypeable #-}
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
-- Module      : Network.AWS.DynamoDB.EnableKinesisStreamingDestination
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
--
-- Starts table data replication to the specified Kinesis data stream at a
-- timestamp chosen during the enable workflow. If this operation doesn\'t
-- return results immediately, use DescribeKinesisStreamingDestination to
-- check if streaming to the Kinesis data stream is ACTIVE.
module Network.AWS.DynamoDB.EnableKinesisStreamingDestination
  ( -- * Creating a Request
    EnableKinesisStreamingDestination (..),
    newEnableKinesisStreamingDestination,

    -- * Request Lenses
    enableKinesisStreamingDestination_tableName,
    enableKinesisStreamingDestination_streamArn,

    -- * Destructuring the Response
    KinesisStreamingDestinationOutput (..),
    newKinesisStreamingDestinationOutput,

    -- * Response Lenses
    kinesisStreamingDestinationOutput_tableName,
    kinesisStreamingDestinationOutput_streamArn,
    kinesisStreamingDestinationOutput_destinationStatus,
  )
where

import Network.AWS.DynamoDB.Types
import qualified Network.AWS.Lens as Lens
import qualified Network.AWS.Prelude as Prelude
import qualified Network.AWS.Request as Request
import qualified Network.AWS.Response as Response

-- | /See:/ 'newEnableKinesisStreamingDestination' smart constructor.
data EnableKinesisStreamingDestination = EnableKinesisStreamingDestination'
  { -- | The name of the DynamoDB table.
    tableName :: Prelude.Text,
    -- | The ARN for a Kinesis data stream.
    streamArn :: Prelude.Text
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Data, Prelude.Typeable, Prelude.Generic)

-- |
-- Create a value of 'EnableKinesisStreamingDestination' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'tableName', 'enableKinesisStreamingDestination_tableName' - The name of the DynamoDB table.
--
-- 'streamArn', 'enableKinesisStreamingDestination_streamArn' - The ARN for a Kinesis data stream.
newEnableKinesisStreamingDestination ::
  -- | 'tableName'
  Prelude.Text ->
  -- | 'streamArn'
  Prelude.Text ->
  EnableKinesisStreamingDestination
newEnableKinesisStreamingDestination
  pTableName_
  pStreamArn_ =
    EnableKinesisStreamingDestination'
      { tableName =
          pTableName_,
        streamArn = pStreamArn_
      }

-- | The name of the DynamoDB table.
enableKinesisStreamingDestination_tableName :: Lens.Lens' EnableKinesisStreamingDestination Prelude.Text
enableKinesisStreamingDestination_tableName = Lens.lens (\EnableKinesisStreamingDestination' {tableName} -> tableName) (\s@EnableKinesisStreamingDestination' {} a -> s {tableName = a} :: EnableKinesisStreamingDestination)

-- | The ARN for a Kinesis data stream.
enableKinesisStreamingDestination_streamArn :: Lens.Lens' EnableKinesisStreamingDestination Prelude.Text
enableKinesisStreamingDestination_streamArn = Lens.lens (\EnableKinesisStreamingDestination' {streamArn} -> streamArn) (\s@EnableKinesisStreamingDestination' {} a -> s {streamArn = a} :: EnableKinesisStreamingDestination)

instance
  Prelude.AWSRequest
    EnableKinesisStreamingDestination
  where
  type
    Rs EnableKinesisStreamingDestination =
      KinesisStreamingDestinationOutput
  request = Request.postJSON defaultService
  response =
    Response.receiveJSON
      (\s h x -> Prelude.eitherParseJSON x)

instance
  Prelude.Hashable
    EnableKinesisStreamingDestination

instance
  Prelude.NFData
    EnableKinesisStreamingDestination

instance
  Prelude.ToHeaders
    EnableKinesisStreamingDestination
  where
  toHeaders =
    Prelude.const
      ( Prelude.mconcat
          [ "X-Amz-Target"
              Prelude.=# ( "DynamoDB_20120810.EnableKinesisStreamingDestination" ::
                             Prelude.ByteString
                         ),
            "Content-Type"
              Prelude.=# ( "application/x-amz-json-1.0" ::
                             Prelude.ByteString
                         )
          ]
      )

instance
  Prelude.ToJSON
    EnableKinesisStreamingDestination
  where
  toJSON EnableKinesisStreamingDestination' {..} =
    Prelude.object
      ( Prelude.catMaybes
          [ Prelude.Just ("TableName" Prelude..= tableName),
            Prelude.Just ("StreamArn" Prelude..= streamArn)
          ]
      )

instance
  Prelude.ToPath
    EnableKinesisStreamingDestination
  where
  toPath = Prelude.const "/"

instance
  Prelude.ToQuery
    EnableKinesisStreamingDestination
  where
  toQuery = Prelude.const Prelude.mempty
