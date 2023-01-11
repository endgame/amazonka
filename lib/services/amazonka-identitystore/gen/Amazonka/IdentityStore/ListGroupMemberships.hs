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
-- Module      : Amazonka.IdentityStore.ListGroupMemberships
-- Copyright   : (c) 2013-2023 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
--
-- For the specified group in the specified identity store, returns the
-- list of all @GroupMembership@ objects and returns results in paginated
-- form.
--
-- This operation returns paginated results.
module Amazonka.IdentityStore.ListGroupMemberships
  ( -- * Creating a Request
    ListGroupMemberships (..),
    newListGroupMemberships,

    -- * Request Lenses
    listGroupMemberships_maxResults,
    listGroupMemberships_nextToken,
    listGroupMemberships_identityStoreId,
    listGroupMemberships_groupId,

    -- * Destructuring the Response
    ListGroupMembershipsResponse (..),
    newListGroupMembershipsResponse,

    -- * Response Lenses
    listGroupMembershipsResponse_nextToken,
    listGroupMembershipsResponse_httpStatus,
    listGroupMembershipsResponse_groupMemberships,
  )
where

import qualified Amazonka.Core as Core
import qualified Amazonka.Core.Lens.Internal as Lens
import qualified Amazonka.Data as Data
import Amazonka.IdentityStore.Types
import qualified Amazonka.Prelude as Prelude
import qualified Amazonka.Request as Request
import qualified Amazonka.Response as Response

-- | /See:/ 'newListGroupMemberships' smart constructor.
data ListGroupMemberships = ListGroupMemberships'
  { -- | The maximum number of results to be returned per request. This parameter
    -- is used in all @List@ requests to specify how many results to return in
    -- one page.
    maxResults :: Prelude.Maybe Prelude.Natural,
    -- | The pagination token used for the @ListUsers@, @ListGroups@ and
    -- @ListGroupMemberships@ API operations. This value is generated by the
    -- identity store service. It is returned in the API response if the total
    -- results are more than the size of one page. This token is also returned
    -- when it is used in the API request to search for the next page.
    nextToken :: Prelude.Maybe Prelude.Text,
    -- | The globally unique identifier for the identity store.
    identityStoreId :: Prelude.Text,
    -- | The identifier for a group in the identity store.
    groupId :: Prelude.Text
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'ListGroupMemberships' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'maxResults', 'listGroupMemberships_maxResults' - The maximum number of results to be returned per request. This parameter
-- is used in all @List@ requests to specify how many results to return in
-- one page.
--
-- 'nextToken', 'listGroupMemberships_nextToken' - The pagination token used for the @ListUsers@, @ListGroups@ and
-- @ListGroupMemberships@ API operations. This value is generated by the
-- identity store service. It is returned in the API response if the total
-- results are more than the size of one page. This token is also returned
-- when it is used in the API request to search for the next page.
--
-- 'identityStoreId', 'listGroupMemberships_identityStoreId' - The globally unique identifier for the identity store.
--
-- 'groupId', 'listGroupMemberships_groupId' - The identifier for a group in the identity store.
newListGroupMemberships ::
  -- | 'identityStoreId'
  Prelude.Text ->
  -- | 'groupId'
  Prelude.Text ->
  ListGroupMemberships
newListGroupMemberships pIdentityStoreId_ pGroupId_ =
  ListGroupMemberships'
    { maxResults = Prelude.Nothing,
      nextToken = Prelude.Nothing,
      identityStoreId = pIdentityStoreId_,
      groupId = pGroupId_
    }

-- | The maximum number of results to be returned per request. This parameter
-- is used in all @List@ requests to specify how many results to return in
-- one page.
listGroupMemberships_maxResults :: Lens.Lens' ListGroupMemberships (Prelude.Maybe Prelude.Natural)
listGroupMemberships_maxResults = Lens.lens (\ListGroupMemberships' {maxResults} -> maxResults) (\s@ListGroupMemberships' {} a -> s {maxResults = a} :: ListGroupMemberships)

-- | The pagination token used for the @ListUsers@, @ListGroups@ and
-- @ListGroupMemberships@ API operations. This value is generated by the
-- identity store service. It is returned in the API response if the total
-- results are more than the size of one page. This token is also returned
-- when it is used in the API request to search for the next page.
listGroupMemberships_nextToken :: Lens.Lens' ListGroupMemberships (Prelude.Maybe Prelude.Text)
listGroupMemberships_nextToken = Lens.lens (\ListGroupMemberships' {nextToken} -> nextToken) (\s@ListGroupMemberships' {} a -> s {nextToken = a} :: ListGroupMemberships)

-- | The globally unique identifier for the identity store.
listGroupMemberships_identityStoreId :: Lens.Lens' ListGroupMemberships Prelude.Text
listGroupMemberships_identityStoreId = Lens.lens (\ListGroupMemberships' {identityStoreId} -> identityStoreId) (\s@ListGroupMemberships' {} a -> s {identityStoreId = a} :: ListGroupMemberships)

-- | The identifier for a group in the identity store.
listGroupMemberships_groupId :: Lens.Lens' ListGroupMemberships Prelude.Text
listGroupMemberships_groupId = Lens.lens (\ListGroupMemberships' {groupId} -> groupId) (\s@ListGroupMemberships' {} a -> s {groupId = a} :: ListGroupMemberships)

instance Core.AWSPager ListGroupMemberships where
  page rq rs
    | Core.stop
        ( rs
            Lens.^? listGroupMembershipsResponse_nextToken
              Prelude.. Lens._Just
        ) =
      Prelude.Nothing
    | Core.stop
        ( rs
            Lens.^. listGroupMembershipsResponse_groupMemberships
        ) =
      Prelude.Nothing
    | Prelude.otherwise =
      Prelude.Just Prelude.$
        rq
          Prelude.& listGroupMemberships_nextToken
          Lens..~ rs
          Lens.^? listGroupMembershipsResponse_nextToken
            Prelude.. Lens._Just

instance Core.AWSRequest ListGroupMemberships where
  type
    AWSResponse ListGroupMemberships =
      ListGroupMembershipsResponse
  request overrides =
    Request.postJSON (overrides defaultService)
  response =
    Response.receiveJSON
      ( \s h x ->
          ListGroupMembershipsResponse'
            Prelude.<$> (x Data..?> "NextToken")
            Prelude.<*> (Prelude.pure (Prelude.fromEnum s))
            Prelude.<*> ( x Data..?> "GroupMemberships"
                            Core..!@ Prelude.mempty
                        )
      )

instance Prelude.Hashable ListGroupMemberships where
  hashWithSalt _salt ListGroupMemberships' {..} =
    _salt `Prelude.hashWithSalt` maxResults
      `Prelude.hashWithSalt` nextToken
      `Prelude.hashWithSalt` identityStoreId
      `Prelude.hashWithSalt` groupId

instance Prelude.NFData ListGroupMemberships where
  rnf ListGroupMemberships' {..} =
    Prelude.rnf maxResults
      `Prelude.seq` Prelude.rnf nextToken
      `Prelude.seq` Prelude.rnf identityStoreId
      `Prelude.seq` Prelude.rnf groupId

instance Data.ToHeaders ListGroupMemberships where
  toHeaders =
    Prelude.const
      ( Prelude.mconcat
          [ "X-Amz-Target"
              Data.=# ( "AWSIdentityStore.ListGroupMemberships" ::
                          Prelude.ByteString
                      ),
            "Content-Type"
              Data.=# ( "application/x-amz-json-1.1" ::
                          Prelude.ByteString
                      )
          ]
      )

instance Data.ToJSON ListGroupMemberships where
  toJSON ListGroupMemberships' {..} =
    Data.object
      ( Prelude.catMaybes
          [ ("MaxResults" Data..=) Prelude.<$> maxResults,
            ("NextToken" Data..=) Prelude.<$> nextToken,
            Prelude.Just
              ("IdentityStoreId" Data..= identityStoreId),
            Prelude.Just ("GroupId" Data..= groupId)
          ]
      )

instance Data.ToPath ListGroupMemberships where
  toPath = Prelude.const "/"

instance Data.ToQuery ListGroupMemberships where
  toQuery = Prelude.const Prelude.mempty

-- | /See:/ 'newListGroupMembershipsResponse' smart constructor.
data ListGroupMembershipsResponse = ListGroupMembershipsResponse'
  { -- | The pagination token used for the @ListUsers@, @ListGroups@, and
    -- @ListGroupMemberships@ API operations. This value is generated by the
    -- identity store service. It is returned in the API response if the total
    -- results are more than the size of one page. This token is also returned
    -- when it is used in the API request to search for the next page.
    nextToken :: Prelude.Maybe Prelude.Text,
    -- | The response's http status code.
    httpStatus :: Prelude.Int,
    -- | A list of @GroupMembership@ objects in the group.
    groupMemberships :: [GroupMembership]
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'ListGroupMembershipsResponse' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'nextToken', 'listGroupMembershipsResponse_nextToken' - The pagination token used for the @ListUsers@, @ListGroups@, and
-- @ListGroupMemberships@ API operations. This value is generated by the
-- identity store service. It is returned in the API response if the total
-- results are more than the size of one page. This token is also returned
-- when it is used in the API request to search for the next page.
--
-- 'httpStatus', 'listGroupMembershipsResponse_httpStatus' - The response's http status code.
--
-- 'groupMemberships', 'listGroupMembershipsResponse_groupMemberships' - A list of @GroupMembership@ objects in the group.
newListGroupMembershipsResponse ::
  -- | 'httpStatus'
  Prelude.Int ->
  ListGroupMembershipsResponse
newListGroupMembershipsResponse pHttpStatus_ =
  ListGroupMembershipsResponse'
    { nextToken =
        Prelude.Nothing,
      httpStatus = pHttpStatus_,
      groupMemberships = Prelude.mempty
    }

-- | The pagination token used for the @ListUsers@, @ListGroups@, and
-- @ListGroupMemberships@ API operations. This value is generated by the
-- identity store service. It is returned in the API response if the total
-- results are more than the size of one page. This token is also returned
-- when it is used in the API request to search for the next page.
listGroupMembershipsResponse_nextToken :: Lens.Lens' ListGroupMembershipsResponse (Prelude.Maybe Prelude.Text)
listGroupMembershipsResponse_nextToken = Lens.lens (\ListGroupMembershipsResponse' {nextToken} -> nextToken) (\s@ListGroupMembershipsResponse' {} a -> s {nextToken = a} :: ListGroupMembershipsResponse)

-- | The response's http status code.
listGroupMembershipsResponse_httpStatus :: Lens.Lens' ListGroupMembershipsResponse Prelude.Int
listGroupMembershipsResponse_httpStatus = Lens.lens (\ListGroupMembershipsResponse' {httpStatus} -> httpStatus) (\s@ListGroupMembershipsResponse' {} a -> s {httpStatus = a} :: ListGroupMembershipsResponse)

-- | A list of @GroupMembership@ objects in the group.
listGroupMembershipsResponse_groupMemberships :: Lens.Lens' ListGroupMembershipsResponse [GroupMembership]
listGroupMembershipsResponse_groupMemberships = Lens.lens (\ListGroupMembershipsResponse' {groupMemberships} -> groupMemberships) (\s@ListGroupMembershipsResponse' {} a -> s {groupMemberships = a} :: ListGroupMembershipsResponse) Prelude.. Lens.coerced

instance Prelude.NFData ListGroupMembershipsResponse where
  rnf ListGroupMembershipsResponse' {..} =
    Prelude.rnf nextToken
      `Prelude.seq` Prelude.rnf httpStatus
      `Prelude.seq` Prelude.rnf groupMemberships
