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
-- Module      : Amazonka.AppStream.DescribeUserStackAssociations
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
--
-- Retrieves a list that describes the UserStackAssociation objects. You
-- must specify either or both of the following:
--
-- -   The stack name
--
-- -   The user name (email address of the user associated with the stack)
--     and the authentication type for the user
--
-- This operation returns paginated results.
module Amazonka.AppStream.DescribeUserStackAssociations
  ( -- * Creating a Request
    DescribeUserStackAssociations (..),
    newDescribeUserStackAssociations,

    -- * Request Lenses
    describeUserStackAssociations_nextToken,
    describeUserStackAssociations_authenticationType,
    describeUserStackAssociations_userName,
    describeUserStackAssociations_stackName,
    describeUserStackAssociations_maxResults,

    -- * Destructuring the Response
    DescribeUserStackAssociationsResponse (..),
    newDescribeUserStackAssociationsResponse,

    -- * Response Lenses
    describeUserStackAssociationsResponse_nextToken,
    describeUserStackAssociationsResponse_userStackAssociations,
    describeUserStackAssociationsResponse_httpStatus,
  )
where

import Amazonka.AppStream.Types
import qualified Amazonka.Core as Core
import qualified Amazonka.Lens as Lens
import qualified Amazonka.Prelude as Prelude
import qualified Amazonka.Request as Request
import qualified Amazonka.Response as Response

-- | /See:/ 'newDescribeUserStackAssociations' smart constructor.
data DescribeUserStackAssociations = DescribeUserStackAssociations'
  { -- | The pagination token to use to retrieve the next page of results for
    -- this operation. If this value is null, it retrieves the first page.
    nextToken :: Prelude.Maybe Prelude.Text,
    -- | The authentication type for the user who is associated with the stack.
    -- You must specify USERPOOL.
    authenticationType :: Prelude.Maybe AuthenticationType,
    -- | The email address of the user who is associated with the stack.
    --
    -- Users\' email addresses are case-sensitive.
    userName :: Prelude.Maybe (Core.Sensitive Prelude.Text),
    -- | The name of the stack that is associated with the user.
    stackName :: Prelude.Maybe Prelude.Text,
    -- | The maximum size of each page of results.
    maxResults :: Prelude.Maybe Prelude.Natural
  }
  deriving (Prelude.Eq, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'DescribeUserStackAssociations' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'nextToken', 'describeUserStackAssociations_nextToken' - The pagination token to use to retrieve the next page of results for
-- this operation. If this value is null, it retrieves the first page.
--
-- 'authenticationType', 'describeUserStackAssociations_authenticationType' - The authentication type for the user who is associated with the stack.
-- You must specify USERPOOL.
--
-- 'userName', 'describeUserStackAssociations_userName' - The email address of the user who is associated with the stack.
--
-- Users\' email addresses are case-sensitive.
--
-- 'stackName', 'describeUserStackAssociations_stackName' - The name of the stack that is associated with the user.
--
-- 'maxResults', 'describeUserStackAssociations_maxResults' - The maximum size of each page of results.
newDescribeUserStackAssociations ::
  DescribeUserStackAssociations
newDescribeUserStackAssociations =
  DescribeUserStackAssociations'
    { nextToken =
        Prelude.Nothing,
      authenticationType = Prelude.Nothing,
      userName = Prelude.Nothing,
      stackName = Prelude.Nothing,
      maxResults = Prelude.Nothing
    }

-- | The pagination token to use to retrieve the next page of results for
-- this operation. If this value is null, it retrieves the first page.
describeUserStackAssociations_nextToken :: Lens.Lens' DescribeUserStackAssociations (Prelude.Maybe Prelude.Text)
describeUserStackAssociations_nextToken = Lens.lens (\DescribeUserStackAssociations' {nextToken} -> nextToken) (\s@DescribeUserStackAssociations' {} a -> s {nextToken = a} :: DescribeUserStackAssociations)

-- | The authentication type for the user who is associated with the stack.
-- You must specify USERPOOL.
describeUserStackAssociations_authenticationType :: Lens.Lens' DescribeUserStackAssociations (Prelude.Maybe AuthenticationType)
describeUserStackAssociations_authenticationType = Lens.lens (\DescribeUserStackAssociations' {authenticationType} -> authenticationType) (\s@DescribeUserStackAssociations' {} a -> s {authenticationType = a} :: DescribeUserStackAssociations)

-- | The email address of the user who is associated with the stack.
--
-- Users\' email addresses are case-sensitive.
describeUserStackAssociations_userName :: Lens.Lens' DescribeUserStackAssociations (Prelude.Maybe Prelude.Text)
describeUserStackAssociations_userName = Lens.lens (\DescribeUserStackAssociations' {userName} -> userName) (\s@DescribeUserStackAssociations' {} a -> s {userName = a} :: DescribeUserStackAssociations) Prelude.. Lens.mapping Core._Sensitive

-- | The name of the stack that is associated with the user.
describeUserStackAssociations_stackName :: Lens.Lens' DescribeUserStackAssociations (Prelude.Maybe Prelude.Text)
describeUserStackAssociations_stackName = Lens.lens (\DescribeUserStackAssociations' {stackName} -> stackName) (\s@DescribeUserStackAssociations' {} a -> s {stackName = a} :: DescribeUserStackAssociations)

-- | The maximum size of each page of results.
describeUserStackAssociations_maxResults :: Lens.Lens' DescribeUserStackAssociations (Prelude.Maybe Prelude.Natural)
describeUserStackAssociations_maxResults = Lens.lens (\DescribeUserStackAssociations' {maxResults} -> maxResults) (\s@DescribeUserStackAssociations' {} a -> s {maxResults = a} :: DescribeUserStackAssociations)

instance Core.AWSPager DescribeUserStackAssociations where
  page rq rs
    | Core.stop
        ( rs
            Lens.^? describeUserStackAssociationsResponse_nextToken
              Prelude.. Lens._Just
        ) =
      Prelude.Nothing
    | Core.stop
        ( rs
            Lens.^? describeUserStackAssociationsResponse_userStackAssociations
              Prelude.. Lens._Just
              Prelude.. Lens.to Prelude.toList
        ) =
      Prelude.Nothing
    | Prelude.otherwise =
      Prelude.Just Prelude.$
        rq
          Prelude.& describeUserStackAssociations_nextToken
          Lens..~ rs
          Lens.^? describeUserStackAssociationsResponse_nextToken
            Prelude.. Lens._Just

instance
  Core.AWSRequest
    DescribeUserStackAssociations
  where
  type
    AWSResponse DescribeUserStackAssociations =
      DescribeUserStackAssociationsResponse
  request = Request.postJSON defaultService
  response =
    Response.receiveJSON
      ( \s h x ->
          DescribeUserStackAssociationsResponse'
            Prelude.<$> (x Core..?> "NextToken")
            Prelude.<*> (x Core..?> "UserStackAssociations")
            Prelude.<*> (Prelude.pure (Prelude.fromEnum s))
      )

instance
  Prelude.Hashable
    DescribeUserStackAssociations
  where
  hashWithSalt _salt DescribeUserStackAssociations' {..} =
    _salt `Prelude.hashWithSalt` nextToken
      `Prelude.hashWithSalt` authenticationType
      `Prelude.hashWithSalt` userName
      `Prelude.hashWithSalt` stackName
      `Prelude.hashWithSalt` maxResults

instance Prelude.NFData DescribeUserStackAssociations where
  rnf DescribeUserStackAssociations' {..} =
    Prelude.rnf nextToken
      `Prelude.seq` Prelude.rnf authenticationType
      `Prelude.seq` Prelude.rnf userName
      `Prelude.seq` Prelude.rnf stackName
      `Prelude.seq` Prelude.rnf maxResults

instance Core.ToHeaders DescribeUserStackAssociations where
  toHeaders =
    Prelude.const
      ( Prelude.mconcat
          [ "X-Amz-Target"
              Core.=# ( "PhotonAdminProxyService.DescribeUserStackAssociations" ::
                          Prelude.ByteString
                      ),
            "Content-Type"
              Core.=# ( "application/x-amz-json-1.1" ::
                          Prelude.ByteString
                      )
          ]
      )

instance Core.ToJSON DescribeUserStackAssociations where
  toJSON DescribeUserStackAssociations' {..} =
    Core.object
      ( Prelude.catMaybes
          [ ("NextToken" Core..=) Prelude.<$> nextToken,
            ("AuthenticationType" Core..=)
              Prelude.<$> authenticationType,
            ("UserName" Core..=) Prelude.<$> userName,
            ("StackName" Core..=) Prelude.<$> stackName,
            ("MaxResults" Core..=) Prelude.<$> maxResults
          ]
      )

instance Core.ToPath DescribeUserStackAssociations where
  toPath = Prelude.const "/"

instance Core.ToQuery DescribeUserStackAssociations where
  toQuery = Prelude.const Prelude.mempty

-- | /See:/ 'newDescribeUserStackAssociationsResponse' smart constructor.
data DescribeUserStackAssociationsResponse = DescribeUserStackAssociationsResponse'
  { -- | The pagination token to use to retrieve the next page of results for
    -- this operation. If there are no more pages, this value is null.
    nextToken :: Prelude.Maybe Prelude.Text,
    -- | The UserStackAssociation objects.
    userStackAssociations :: Prelude.Maybe (Prelude.NonEmpty UserStackAssociation),
    -- | The response's http status code.
    httpStatus :: Prelude.Int
  }
  deriving (Prelude.Eq, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'DescribeUserStackAssociationsResponse' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'nextToken', 'describeUserStackAssociationsResponse_nextToken' - The pagination token to use to retrieve the next page of results for
-- this operation. If there are no more pages, this value is null.
--
-- 'userStackAssociations', 'describeUserStackAssociationsResponse_userStackAssociations' - The UserStackAssociation objects.
--
-- 'httpStatus', 'describeUserStackAssociationsResponse_httpStatus' - The response's http status code.
newDescribeUserStackAssociationsResponse ::
  -- | 'httpStatus'
  Prelude.Int ->
  DescribeUserStackAssociationsResponse
newDescribeUserStackAssociationsResponse pHttpStatus_ =
  DescribeUserStackAssociationsResponse'
    { nextToken =
        Prelude.Nothing,
      userStackAssociations =
        Prelude.Nothing,
      httpStatus = pHttpStatus_
    }

-- | The pagination token to use to retrieve the next page of results for
-- this operation. If there are no more pages, this value is null.
describeUserStackAssociationsResponse_nextToken :: Lens.Lens' DescribeUserStackAssociationsResponse (Prelude.Maybe Prelude.Text)
describeUserStackAssociationsResponse_nextToken = Lens.lens (\DescribeUserStackAssociationsResponse' {nextToken} -> nextToken) (\s@DescribeUserStackAssociationsResponse' {} a -> s {nextToken = a} :: DescribeUserStackAssociationsResponse)

-- | The UserStackAssociation objects.
describeUserStackAssociationsResponse_userStackAssociations :: Lens.Lens' DescribeUserStackAssociationsResponse (Prelude.Maybe (Prelude.NonEmpty UserStackAssociation))
describeUserStackAssociationsResponse_userStackAssociations = Lens.lens (\DescribeUserStackAssociationsResponse' {userStackAssociations} -> userStackAssociations) (\s@DescribeUserStackAssociationsResponse' {} a -> s {userStackAssociations = a} :: DescribeUserStackAssociationsResponse) Prelude.. Lens.mapping Lens.coerced

-- | The response's http status code.
describeUserStackAssociationsResponse_httpStatus :: Lens.Lens' DescribeUserStackAssociationsResponse Prelude.Int
describeUserStackAssociationsResponse_httpStatus = Lens.lens (\DescribeUserStackAssociationsResponse' {httpStatus} -> httpStatus) (\s@DescribeUserStackAssociationsResponse' {} a -> s {httpStatus = a} :: DescribeUserStackAssociationsResponse)

instance
  Prelude.NFData
    DescribeUserStackAssociationsResponse
  where
  rnf DescribeUserStackAssociationsResponse' {..} =
    Prelude.rnf nextToken
      `Prelude.seq` Prelude.rnf userStackAssociations
      `Prelude.seq` Prelude.rnf httpStatus
