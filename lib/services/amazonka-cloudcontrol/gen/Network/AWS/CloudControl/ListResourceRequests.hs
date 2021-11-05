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
-- Module      : Amazonka.CloudControl.ListResourceRequests
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
--
-- Returns existing resource operation requests. This includes requests of
-- all status types. For more information, see
-- <https://docs.aws.amazon.com/cloudcontrolapi/latest/userguide/resource-operations-manage-requests.html#resource-operations-manage-requests-list Listing active resource operation requests>
-- in the /Amazon Web Services Cloud Control API User Guide/.
--
-- Resource operation requests expire after seven days.
module Amazonka.CloudControl.ListResourceRequests
  ( -- * Creating a Request
    ListResourceRequests (..),
    newListResourceRequests,

    -- * Request Lenses
    listResourceRequests_nextToken,
    listResourceRequests_resourceRequestStatusFilter,
    listResourceRequests_maxResults,

    -- * Destructuring the Response
    ListResourceRequestsResponse (..),
    newListResourceRequestsResponse,

    -- * Response Lenses
    listResourceRequestsResponse_resourceRequestStatusSummaries,
    listResourceRequestsResponse_nextToken,
    listResourceRequestsResponse_httpStatus,
  )
where

import Amazonka.CloudControl.Types
import qualified Amazonka.Core as Core
import qualified Amazonka.Lens as Lens
import qualified Amazonka.Prelude as Prelude
import qualified Amazonka.Request as Request
import qualified Amazonka.Response as Response

-- | /See:/ 'newListResourceRequests' smart constructor.
data ListResourceRequests = ListResourceRequests'
  { -- | If the previous paginated request didn\'t return all of the remaining
    -- results, the response object\'s @NextToken@ parameter value is set to a
    -- token. To retrieve the next set of results, call this action again and
    -- assign that token to the request object\'s @NextToken@ parameter. If
    -- there are no remaining results, the previous response object\'s
    -- @NextToken@ parameter is set to @null@.
    nextToken :: Prelude.Maybe Prelude.Text,
    -- | The filter criteria to apply to the requests returned.
    resourceRequestStatusFilter :: Prelude.Maybe ResourceRequestStatusFilter,
    -- | The maximum number of results to be returned with a single call. If the
    -- number of available results exceeds this maximum, the response includes
    -- a @NextToken@ value that you can assign to the @NextToken@ request
    -- parameter to get the next set of results.
    --
    -- The default is @20@.
    maxResults :: Prelude.Maybe Prelude.Natural
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'ListResourceRequests' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'nextToken', 'listResourceRequests_nextToken' - If the previous paginated request didn\'t return all of the remaining
-- results, the response object\'s @NextToken@ parameter value is set to a
-- token. To retrieve the next set of results, call this action again and
-- assign that token to the request object\'s @NextToken@ parameter. If
-- there are no remaining results, the previous response object\'s
-- @NextToken@ parameter is set to @null@.
--
-- 'resourceRequestStatusFilter', 'listResourceRequests_resourceRequestStatusFilter' - The filter criteria to apply to the requests returned.
--
-- 'maxResults', 'listResourceRequests_maxResults' - The maximum number of results to be returned with a single call. If the
-- number of available results exceeds this maximum, the response includes
-- a @NextToken@ value that you can assign to the @NextToken@ request
-- parameter to get the next set of results.
--
-- The default is @20@.
newListResourceRequests ::
  ListResourceRequests
newListResourceRequests =
  ListResourceRequests'
    { nextToken = Prelude.Nothing,
      resourceRequestStatusFilter = Prelude.Nothing,
      maxResults = Prelude.Nothing
    }

-- | If the previous paginated request didn\'t return all of the remaining
-- results, the response object\'s @NextToken@ parameter value is set to a
-- token. To retrieve the next set of results, call this action again and
-- assign that token to the request object\'s @NextToken@ parameter. If
-- there are no remaining results, the previous response object\'s
-- @NextToken@ parameter is set to @null@.
listResourceRequests_nextToken :: Lens.Lens' ListResourceRequests (Prelude.Maybe Prelude.Text)
listResourceRequests_nextToken = Lens.lens (\ListResourceRequests' {nextToken} -> nextToken) (\s@ListResourceRequests' {} a -> s {nextToken = a} :: ListResourceRequests)

-- | The filter criteria to apply to the requests returned.
listResourceRequests_resourceRequestStatusFilter :: Lens.Lens' ListResourceRequests (Prelude.Maybe ResourceRequestStatusFilter)
listResourceRequests_resourceRequestStatusFilter = Lens.lens (\ListResourceRequests' {resourceRequestStatusFilter} -> resourceRequestStatusFilter) (\s@ListResourceRequests' {} a -> s {resourceRequestStatusFilter = a} :: ListResourceRequests)

-- | The maximum number of results to be returned with a single call. If the
-- number of available results exceeds this maximum, the response includes
-- a @NextToken@ value that you can assign to the @NextToken@ request
-- parameter to get the next set of results.
--
-- The default is @20@.
listResourceRequests_maxResults :: Lens.Lens' ListResourceRequests (Prelude.Maybe Prelude.Natural)
listResourceRequests_maxResults = Lens.lens (\ListResourceRequests' {maxResults} -> maxResults) (\s@ListResourceRequests' {} a -> s {maxResults = a} :: ListResourceRequests)

instance Core.AWSRequest ListResourceRequests where
  type
    AWSResponse ListResourceRequests =
      ListResourceRequestsResponse
  request = Request.postJSON defaultService
  response =
    Response.receiveJSON
      ( \s h x ->
          ListResourceRequestsResponse'
            Prelude.<$> ( x Core..?> "ResourceRequestStatusSummaries"
                            Core..!@ Prelude.mempty
                        )
            Prelude.<*> (x Core..?> "NextToken")
            Prelude.<*> (Prelude.pure (Prelude.fromEnum s))
      )

instance Prelude.Hashable ListResourceRequests

instance Prelude.NFData ListResourceRequests

instance Core.ToHeaders ListResourceRequests where
  toHeaders =
    Prelude.const
      ( Prelude.mconcat
          [ "X-Amz-Target"
              Core.=# ( "CloudApiService.ListResourceRequests" ::
                          Prelude.ByteString
                      ),
            "Content-Type"
              Core.=# ( "application/x-amz-json-1.0" ::
                          Prelude.ByteString
                      )
          ]
      )

instance Core.ToJSON ListResourceRequests where
  toJSON ListResourceRequests' {..} =
    Core.object
      ( Prelude.catMaybes
          [ ("NextToken" Core..=) Prelude.<$> nextToken,
            ("ResourceRequestStatusFilter" Core..=)
              Prelude.<$> resourceRequestStatusFilter,
            ("MaxResults" Core..=) Prelude.<$> maxResults
          ]
      )

instance Core.ToPath ListResourceRequests where
  toPath = Prelude.const "/"

instance Core.ToQuery ListResourceRequests where
  toQuery = Prelude.const Prelude.mempty

-- | /See:/ 'newListResourceRequestsResponse' smart constructor.
data ListResourceRequestsResponse = ListResourceRequestsResponse'
  { -- | The requests that match the specified filter criteria.
    resourceRequestStatusSummaries :: Prelude.Maybe [ProgressEvent],
    -- | If the request doesn\'t return all of the remaining results, @NextToken@
    -- is set to a token. To retrieve the next set of results, call
    -- @ListResources@ again and assign that token to the request object\'s
    -- @NextToken@ parameter. If the request returns all results, @NextToken@
    -- is set to null.
    nextToken :: Prelude.Maybe Prelude.Text,
    -- | The response's http status code.
    httpStatus :: Prelude.Int
  }
  deriving (Prelude.Eq, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'ListResourceRequestsResponse' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'resourceRequestStatusSummaries', 'listResourceRequestsResponse_resourceRequestStatusSummaries' - The requests that match the specified filter criteria.
--
-- 'nextToken', 'listResourceRequestsResponse_nextToken' - If the request doesn\'t return all of the remaining results, @NextToken@
-- is set to a token. To retrieve the next set of results, call
-- @ListResources@ again and assign that token to the request object\'s
-- @NextToken@ parameter. If the request returns all results, @NextToken@
-- is set to null.
--
-- 'httpStatus', 'listResourceRequestsResponse_httpStatus' - The response's http status code.
newListResourceRequestsResponse ::
  -- | 'httpStatus'
  Prelude.Int ->
  ListResourceRequestsResponse
newListResourceRequestsResponse pHttpStatus_ =
  ListResourceRequestsResponse'
    { resourceRequestStatusSummaries =
        Prelude.Nothing,
      nextToken = Prelude.Nothing,
      httpStatus = pHttpStatus_
    }

-- | The requests that match the specified filter criteria.
listResourceRequestsResponse_resourceRequestStatusSummaries :: Lens.Lens' ListResourceRequestsResponse (Prelude.Maybe [ProgressEvent])
listResourceRequestsResponse_resourceRequestStatusSummaries = Lens.lens (\ListResourceRequestsResponse' {resourceRequestStatusSummaries} -> resourceRequestStatusSummaries) (\s@ListResourceRequestsResponse' {} a -> s {resourceRequestStatusSummaries = a} :: ListResourceRequestsResponse) Prelude.. Lens.mapping Lens.coerced

-- | If the request doesn\'t return all of the remaining results, @NextToken@
-- is set to a token. To retrieve the next set of results, call
-- @ListResources@ again and assign that token to the request object\'s
-- @NextToken@ parameter. If the request returns all results, @NextToken@
-- is set to null.
listResourceRequestsResponse_nextToken :: Lens.Lens' ListResourceRequestsResponse (Prelude.Maybe Prelude.Text)
listResourceRequestsResponse_nextToken = Lens.lens (\ListResourceRequestsResponse' {nextToken} -> nextToken) (\s@ListResourceRequestsResponse' {} a -> s {nextToken = a} :: ListResourceRequestsResponse)

-- | The response's http status code.
listResourceRequestsResponse_httpStatus :: Lens.Lens' ListResourceRequestsResponse Prelude.Int
listResourceRequestsResponse_httpStatus = Lens.lens (\ListResourceRequestsResponse' {httpStatus} -> httpStatus) (\s@ListResourceRequestsResponse' {} a -> s {httpStatus = a} :: ListResourceRequestsResponse)

instance Prelude.NFData ListResourceRequestsResponse
