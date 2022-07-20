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
-- Module      : Amazonka.EMRContainers.ListVirtualClusters
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
--
-- Lists information about the specified virtual cluster. Virtual cluster
-- is a managed entity on Amazon EMR on EKS. You can create, describe, list
-- and delete virtual clusters. They do not consume any additional resource
-- in your system. A single virtual cluster maps to a single Kubernetes
-- namespace. Given this relationship, you can model virtual clusters the
-- same way you model Kubernetes namespaces to meet your requirements.
--
-- This operation returns paginated results.
module Amazonka.EMRContainers.ListVirtualClusters
  ( -- * Creating a Request
    ListVirtualClusters (..),
    newListVirtualClusters,

    -- * Request Lenses
    listVirtualClusters_nextToken,
    listVirtualClusters_createdBefore,
    listVirtualClusters_containerProviderType,
    listVirtualClusters_maxResults,
    listVirtualClusters_containerProviderId,
    listVirtualClusters_createdAfter,
    listVirtualClusters_states,

    -- * Destructuring the Response
    ListVirtualClustersResponse (..),
    newListVirtualClustersResponse,

    -- * Response Lenses
    listVirtualClustersResponse_nextToken,
    listVirtualClustersResponse_virtualClusters,
    listVirtualClustersResponse_httpStatus,
  )
where

import qualified Amazonka.Core as Core
import Amazonka.EMRContainers.Types
import qualified Amazonka.Lens as Lens
import qualified Amazonka.Prelude as Prelude
import qualified Amazonka.Request as Request
import qualified Amazonka.Response as Response

-- | /See:/ 'newListVirtualClusters' smart constructor.
data ListVirtualClusters = ListVirtualClusters'
  { -- | The token for the next set of virtual clusters to return.
    nextToken :: Prelude.Maybe Prelude.Text,
    -- | The date and time before which the virtual clusters are created.
    createdBefore :: Prelude.Maybe Core.POSIX,
    -- | The container provider type of the virtual cluster. EKS is the only
    -- supported type as of now.
    containerProviderType :: Prelude.Maybe ContainerProviderType,
    -- | The maximum number of virtual clusters that can be listed.
    maxResults :: Prelude.Maybe Prelude.Int,
    -- | The container provider ID of the virtual cluster.
    containerProviderId :: Prelude.Maybe Prelude.Text,
    -- | The date and time after which the virtual clusters are created.
    createdAfter :: Prelude.Maybe Core.POSIX,
    -- | The states of the requested virtual clusters.
    states :: Prelude.Maybe [VirtualClusterState]
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'ListVirtualClusters' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'nextToken', 'listVirtualClusters_nextToken' - The token for the next set of virtual clusters to return.
--
-- 'createdBefore', 'listVirtualClusters_createdBefore' - The date and time before which the virtual clusters are created.
--
-- 'containerProviderType', 'listVirtualClusters_containerProviderType' - The container provider type of the virtual cluster. EKS is the only
-- supported type as of now.
--
-- 'maxResults', 'listVirtualClusters_maxResults' - The maximum number of virtual clusters that can be listed.
--
-- 'containerProviderId', 'listVirtualClusters_containerProviderId' - The container provider ID of the virtual cluster.
--
-- 'createdAfter', 'listVirtualClusters_createdAfter' - The date and time after which the virtual clusters are created.
--
-- 'states', 'listVirtualClusters_states' - The states of the requested virtual clusters.
newListVirtualClusters ::
  ListVirtualClusters
newListVirtualClusters =
  ListVirtualClusters'
    { nextToken = Prelude.Nothing,
      createdBefore = Prelude.Nothing,
      containerProviderType = Prelude.Nothing,
      maxResults = Prelude.Nothing,
      containerProviderId = Prelude.Nothing,
      createdAfter = Prelude.Nothing,
      states = Prelude.Nothing
    }

-- | The token for the next set of virtual clusters to return.
listVirtualClusters_nextToken :: Lens.Lens' ListVirtualClusters (Prelude.Maybe Prelude.Text)
listVirtualClusters_nextToken = Lens.lens (\ListVirtualClusters' {nextToken} -> nextToken) (\s@ListVirtualClusters' {} a -> s {nextToken = a} :: ListVirtualClusters)

-- | The date and time before which the virtual clusters are created.
listVirtualClusters_createdBefore :: Lens.Lens' ListVirtualClusters (Prelude.Maybe Prelude.UTCTime)
listVirtualClusters_createdBefore = Lens.lens (\ListVirtualClusters' {createdBefore} -> createdBefore) (\s@ListVirtualClusters' {} a -> s {createdBefore = a} :: ListVirtualClusters) Prelude.. Lens.mapping Core._Time

-- | The container provider type of the virtual cluster. EKS is the only
-- supported type as of now.
listVirtualClusters_containerProviderType :: Lens.Lens' ListVirtualClusters (Prelude.Maybe ContainerProviderType)
listVirtualClusters_containerProviderType = Lens.lens (\ListVirtualClusters' {containerProviderType} -> containerProviderType) (\s@ListVirtualClusters' {} a -> s {containerProviderType = a} :: ListVirtualClusters)

-- | The maximum number of virtual clusters that can be listed.
listVirtualClusters_maxResults :: Lens.Lens' ListVirtualClusters (Prelude.Maybe Prelude.Int)
listVirtualClusters_maxResults = Lens.lens (\ListVirtualClusters' {maxResults} -> maxResults) (\s@ListVirtualClusters' {} a -> s {maxResults = a} :: ListVirtualClusters)

-- | The container provider ID of the virtual cluster.
listVirtualClusters_containerProviderId :: Lens.Lens' ListVirtualClusters (Prelude.Maybe Prelude.Text)
listVirtualClusters_containerProviderId = Lens.lens (\ListVirtualClusters' {containerProviderId} -> containerProviderId) (\s@ListVirtualClusters' {} a -> s {containerProviderId = a} :: ListVirtualClusters)

-- | The date and time after which the virtual clusters are created.
listVirtualClusters_createdAfter :: Lens.Lens' ListVirtualClusters (Prelude.Maybe Prelude.UTCTime)
listVirtualClusters_createdAfter = Lens.lens (\ListVirtualClusters' {createdAfter} -> createdAfter) (\s@ListVirtualClusters' {} a -> s {createdAfter = a} :: ListVirtualClusters) Prelude.. Lens.mapping Core._Time

-- | The states of the requested virtual clusters.
listVirtualClusters_states :: Lens.Lens' ListVirtualClusters (Prelude.Maybe [VirtualClusterState])
listVirtualClusters_states = Lens.lens (\ListVirtualClusters' {states} -> states) (\s@ListVirtualClusters' {} a -> s {states = a} :: ListVirtualClusters) Prelude.. Lens.mapping Lens.coerced

instance Core.AWSPager ListVirtualClusters where
  page rq rs
    | Core.stop
        ( rs
            Lens.^? listVirtualClustersResponse_nextToken
              Prelude.. Lens._Just
        ) =
      Prelude.Nothing
    | Core.stop
        ( rs
            Lens.^? listVirtualClustersResponse_virtualClusters
              Prelude.. Lens._Just
        ) =
      Prelude.Nothing
    | Prelude.otherwise =
      Prelude.Just Prelude.$
        rq
          Prelude.& listVirtualClusters_nextToken
          Lens..~ rs
          Lens.^? listVirtualClustersResponse_nextToken
            Prelude.. Lens._Just

instance Core.AWSRequest ListVirtualClusters where
  type
    AWSResponse ListVirtualClusters =
      ListVirtualClustersResponse
  request = Request.get defaultService
  response =
    Response.receiveJSON
      ( \s h x ->
          ListVirtualClustersResponse'
            Prelude.<$> (x Core..?> "nextToken")
            Prelude.<*> ( x Core..?> "virtualClusters"
                            Core..!@ Prelude.mempty
                        )
            Prelude.<*> (Prelude.pure (Prelude.fromEnum s))
      )

instance Prelude.Hashable ListVirtualClusters where
  hashWithSalt _salt ListVirtualClusters' {..} =
    _salt `Prelude.hashWithSalt` nextToken
      `Prelude.hashWithSalt` createdBefore
      `Prelude.hashWithSalt` containerProviderType
      `Prelude.hashWithSalt` maxResults
      `Prelude.hashWithSalt` containerProviderId
      `Prelude.hashWithSalt` createdAfter
      `Prelude.hashWithSalt` states

instance Prelude.NFData ListVirtualClusters where
  rnf ListVirtualClusters' {..} =
    Prelude.rnf nextToken
      `Prelude.seq` Prelude.rnf createdBefore
      `Prelude.seq` Prelude.rnf containerProviderType
      `Prelude.seq` Prelude.rnf maxResults
      `Prelude.seq` Prelude.rnf containerProviderId
      `Prelude.seq` Prelude.rnf createdAfter
      `Prelude.seq` Prelude.rnf states

instance Core.ToHeaders ListVirtualClusters where
  toHeaders =
    Prelude.const
      ( Prelude.mconcat
          [ "Content-Type"
              Core.=# ( "application/x-amz-json-1.1" ::
                          Prelude.ByteString
                      )
          ]
      )

instance Core.ToPath ListVirtualClusters where
  toPath = Prelude.const "/virtualclusters"

instance Core.ToQuery ListVirtualClusters where
  toQuery ListVirtualClusters' {..} =
    Prelude.mconcat
      [ "nextToken" Core.=: nextToken,
        "createdBefore" Core.=: createdBefore,
        "containerProviderType"
          Core.=: containerProviderType,
        "maxResults" Core.=: maxResults,
        "containerProviderId" Core.=: containerProviderId,
        "createdAfter" Core.=: createdAfter,
        "states"
          Core.=: Core.toQuery
            (Core.toQueryList "member" Prelude.<$> states)
      ]

-- | /See:/ 'newListVirtualClustersResponse' smart constructor.
data ListVirtualClustersResponse = ListVirtualClustersResponse'
  { -- | This output displays the token for the next set of virtual clusters.
    nextToken :: Prelude.Maybe Prelude.Text,
    -- | This output lists the specified virtual clusters.
    virtualClusters :: Prelude.Maybe [VirtualCluster],
    -- | The response's http status code.
    httpStatus :: Prelude.Int
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'ListVirtualClustersResponse' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'nextToken', 'listVirtualClustersResponse_nextToken' - This output displays the token for the next set of virtual clusters.
--
-- 'virtualClusters', 'listVirtualClustersResponse_virtualClusters' - This output lists the specified virtual clusters.
--
-- 'httpStatus', 'listVirtualClustersResponse_httpStatus' - The response's http status code.
newListVirtualClustersResponse ::
  -- | 'httpStatus'
  Prelude.Int ->
  ListVirtualClustersResponse
newListVirtualClustersResponse pHttpStatus_ =
  ListVirtualClustersResponse'
    { nextToken =
        Prelude.Nothing,
      virtualClusters = Prelude.Nothing,
      httpStatus = pHttpStatus_
    }

-- | This output displays the token for the next set of virtual clusters.
listVirtualClustersResponse_nextToken :: Lens.Lens' ListVirtualClustersResponse (Prelude.Maybe Prelude.Text)
listVirtualClustersResponse_nextToken = Lens.lens (\ListVirtualClustersResponse' {nextToken} -> nextToken) (\s@ListVirtualClustersResponse' {} a -> s {nextToken = a} :: ListVirtualClustersResponse)

-- | This output lists the specified virtual clusters.
listVirtualClustersResponse_virtualClusters :: Lens.Lens' ListVirtualClustersResponse (Prelude.Maybe [VirtualCluster])
listVirtualClustersResponse_virtualClusters = Lens.lens (\ListVirtualClustersResponse' {virtualClusters} -> virtualClusters) (\s@ListVirtualClustersResponse' {} a -> s {virtualClusters = a} :: ListVirtualClustersResponse) Prelude.. Lens.mapping Lens.coerced

-- | The response's http status code.
listVirtualClustersResponse_httpStatus :: Lens.Lens' ListVirtualClustersResponse Prelude.Int
listVirtualClustersResponse_httpStatus = Lens.lens (\ListVirtualClustersResponse' {httpStatus} -> httpStatus) (\s@ListVirtualClustersResponse' {} a -> s {httpStatus = a} :: ListVirtualClustersResponse)

instance Prelude.NFData ListVirtualClustersResponse where
  rnf ListVirtualClustersResponse' {..} =
    Prelude.rnf nextToken
      `Prelude.seq` Prelude.rnf virtualClusters
      `Prelude.seq` Prelude.rnf httpStatus
