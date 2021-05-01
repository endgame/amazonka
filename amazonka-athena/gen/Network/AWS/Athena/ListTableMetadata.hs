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
-- Module      : Network.AWS.Athena.ListTableMetadata
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
--
-- Lists the metadata for the tables in the specified data catalog
-- database.
--
-- This operation returns paginated results.
module Network.AWS.Athena.ListTableMetadata
  ( -- * Creating a Request
    ListTableMetadata (..),
    newListTableMetadata,

    -- * Request Lenses
    listTableMetadata_nextToken,
    listTableMetadata_maxResults,
    listTableMetadata_expression,
    listTableMetadata_catalogName,
    listTableMetadata_databaseName,

    -- * Destructuring the Response
    ListTableMetadataResponse (..),
    newListTableMetadataResponse,

    -- * Response Lenses
    listTableMetadataResponse_nextToken,
    listTableMetadataResponse_tableMetadataList,
    listTableMetadataResponse_httpStatus,
  )
where

import Network.AWS.Athena.Types
import qualified Network.AWS.Lens as Lens
import qualified Network.AWS.Pager as Pager
import qualified Network.AWS.Prelude as Prelude
import qualified Network.AWS.Request as Request
import qualified Network.AWS.Response as Response

-- | /See:/ 'newListTableMetadata' smart constructor.
data ListTableMetadata = ListTableMetadata'
  { -- | A token generated by the Athena service that specifies where to continue
    -- pagination if a previous request was truncated. To obtain the next set
    -- of pages, pass in the NextToken from the response object of the previous
    -- page call.
    nextToken :: Prelude.Maybe Prelude.Text,
    -- | Specifies the maximum number of results to return.
    maxResults :: Prelude.Maybe Prelude.Natural,
    -- | A regex filter that pattern-matches table names. If no expression is
    -- supplied, metadata for all tables are listed.
    expression :: Prelude.Maybe Prelude.Text,
    -- | The name of the data catalog for which table metadata should be
    -- returned.
    catalogName :: Prelude.Text,
    -- | The name of the database for which table metadata should be returned.
    databaseName :: Prelude.Text
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Data, Prelude.Typeable, Prelude.Generic)

-- |
-- Create a value of 'ListTableMetadata' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'nextToken', 'listTableMetadata_nextToken' - A token generated by the Athena service that specifies where to continue
-- pagination if a previous request was truncated. To obtain the next set
-- of pages, pass in the NextToken from the response object of the previous
-- page call.
--
-- 'maxResults', 'listTableMetadata_maxResults' - Specifies the maximum number of results to return.
--
-- 'expression', 'listTableMetadata_expression' - A regex filter that pattern-matches table names. If no expression is
-- supplied, metadata for all tables are listed.
--
-- 'catalogName', 'listTableMetadata_catalogName' - The name of the data catalog for which table metadata should be
-- returned.
--
-- 'databaseName', 'listTableMetadata_databaseName' - The name of the database for which table metadata should be returned.
newListTableMetadata ::
  -- | 'catalogName'
  Prelude.Text ->
  -- | 'databaseName'
  Prelude.Text ->
  ListTableMetadata
newListTableMetadata pCatalogName_ pDatabaseName_ =
  ListTableMetadata'
    { nextToken = Prelude.Nothing,
      maxResults = Prelude.Nothing,
      expression = Prelude.Nothing,
      catalogName = pCatalogName_,
      databaseName = pDatabaseName_
    }

-- | A token generated by the Athena service that specifies where to continue
-- pagination if a previous request was truncated. To obtain the next set
-- of pages, pass in the NextToken from the response object of the previous
-- page call.
listTableMetadata_nextToken :: Lens.Lens' ListTableMetadata (Prelude.Maybe Prelude.Text)
listTableMetadata_nextToken = Lens.lens (\ListTableMetadata' {nextToken} -> nextToken) (\s@ListTableMetadata' {} a -> s {nextToken = a} :: ListTableMetadata)

-- | Specifies the maximum number of results to return.
listTableMetadata_maxResults :: Lens.Lens' ListTableMetadata (Prelude.Maybe Prelude.Natural)
listTableMetadata_maxResults = Lens.lens (\ListTableMetadata' {maxResults} -> maxResults) (\s@ListTableMetadata' {} a -> s {maxResults = a} :: ListTableMetadata)

-- | A regex filter that pattern-matches table names. If no expression is
-- supplied, metadata for all tables are listed.
listTableMetadata_expression :: Lens.Lens' ListTableMetadata (Prelude.Maybe Prelude.Text)
listTableMetadata_expression = Lens.lens (\ListTableMetadata' {expression} -> expression) (\s@ListTableMetadata' {} a -> s {expression = a} :: ListTableMetadata)

-- | The name of the data catalog for which table metadata should be
-- returned.
listTableMetadata_catalogName :: Lens.Lens' ListTableMetadata Prelude.Text
listTableMetadata_catalogName = Lens.lens (\ListTableMetadata' {catalogName} -> catalogName) (\s@ListTableMetadata' {} a -> s {catalogName = a} :: ListTableMetadata)

-- | The name of the database for which table metadata should be returned.
listTableMetadata_databaseName :: Lens.Lens' ListTableMetadata Prelude.Text
listTableMetadata_databaseName = Lens.lens (\ListTableMetadata' {databaseName} -> databaseName) (\s@ListTableMetadata' {} a -> s {databaseName = a} :: ListTableMetadata)

instance Pager.AWSPager ListTableMetadata where
  page rq rs
    | Pager.stop
        ( rs
            Lens.^? listTableMetadataResponse_nextToken
              Prelude.. Lens._Just
        ) =
      Prelude.Nothing
    | Pager.stop
        ( rs
            Lens.^? listTableMetadataResponse_tableMetadataList
              Prelude.. Lens._Just
        ) =
      Prelude.Nothing
    | Prelude.otherwise =
      Prelude.Just Prelude.$
        rq
          Lens.& listTableMetadata_nextToken
          Lens..~ rs
          Lens.^? listTableMetadataResponse_nextToken
            Prelude.. Lens._Just

instance Prelude.AWSRequest ListTableMetadata where
  type Rs ListTableMetadata = ListTableMetadataResponse
  request = Request.postJSON defaultService
  response =
    Response.receiveJSON
      ( \s h x ->
          ListTableMetadataResponse'
            Prelude.<$> (x Prelude..?> "NextToken")
            Prelude.<*> ( x Prelude..?> "TableMetadataList"
                            Prelude..!@ Prelude.mempty
                        )
            Prelude.<*> (Prelude.pure (Prelude.fromEnum s))
      )

instance Prelude.Hashable ListTableMetadata

instance Prelude.NFData ListTableMetadata

instance Prelude.ToHeaders ListTableMetadata where
  toHeaders =
    Prelude.const
      ( Prelude.mconcat
          [ "X-Amz-Target"
              Prelude.=# ( "AmazonAthena.ListTableMetadata" ::
                             Prelude.ByteString
                         ),
            "Content-Type"
              Prelude.=# ( "application/x-amz-json-1.1" ::
                             Prelude.ByteString
                         )
          ]
      )

instance Prelude.ToJSON ListTableMetadata where
  toJSON ListTableMetadata' {..} =
    Prelude.object
      ( Prelude.catMaybes
          [ ("NextToken" Prelude..=) Prelude.<$> nextToken,
            ("MaxResults" Prelude..=) Prelude.<$> maxResults,
            ("Expression" Prelude..=) Prelude.<$> expression,
            Prelude.Just ("CatalogName" Prelude..= catalogName),
            Prelude.Just
              ("DatabaseName" Prelude..= databaseName)
          ]
      )

instance Prelude.ToPath ListTableMetadata where
  toPath = Prelude.const "/"

instance Prelude.ToQuery ListTableMetadata where
  toQuery = Prelude.const Prelude.mempty

-- | /See:/ 'newListTableMetadataResponse' smart constructor.
data ListTableMetadataResponse = ListTableMetadataResponse'
  { -- | A token generated by the Athena service that specifies where to continue
    -- pagination if a previous request was truncated. To obtain the next set
    -- of pages, pass in the NextToken from the response object of the previous
    -- page call.
    nextToken :: Prelude.Maybe Prelude.Text,
    -- | A list of table metadata.
    tableMetadataList :: Prelude.Maybe [TableMetadata],
    -- | The response's http status code.
    httpStatus :: Prelude.Int
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Data, Prelude.Typeable, Prelude.Generic)

-- |
-- Create a value of 'ListTableMetadataResponse' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'nextToken', 'listTableMetadataResponse_nextToken' - A token generated by the Athena service that specifies where to continue
-- pagination if a previous request was truncated. To obtain the next set
-- of pages, pass in the NextToken from the response object of the previous
-- page call.
--
-- 'tableMetadataList', 'listTableMetadataResponse_tableMetadataList' - A list of table metadata.
--
-- 'httpStatus', 'listTableMetadataResponse_httpStatus' - The response's http status code.
newListTableMetadataResponse ::
  -- | 'httpStatus'
  Prelude.Int ->
  ListTableMetadataResponse
newListTableMetadataResponse pHttpStatus_ =
  ListTableMetadataResponse'
    { nextToken =
        Prelude.Nothing,
      tableMetadataList = Prelude.Nothing,
      httpStatus = pHttpStatus_
    }

-- | A token generated by the Athena service that specifies where to continue
-- pagination if a previous request was truncated. To obtain the next set
-- of pages, pass in the NextToken from the response object of the previous
-- page call.
listTableMetadataResponse_nextToken :: Lens.Lens' ListTableMetadataResponse (Prelude.Maybe Prelude.Text)
listTableMetadataResponse_nextToken = Lens.lens (\ListTableMetadataResponse' {nextToken} -> nextToken) (\s@ListTableMetadataResponse' {} a -> s {nextToken = a} :: ListTableMetadataResponse)

-- | A list of table metadata.
listTableMetadataResponse_tableMetadataList :: Lens.Lens' ListTableMetadataResponse (Prelude.Maybe [TableMetadata])
listTableMetadataResponse_tableMetadataList = Lens.lens (\ListTableMetadataResponse' {tableMetadataList} -> tableMetadataList) (\s@ListTableMetadataResponse' {} a -> s {tableMetadataList = a} :: ListTableMetadataResponse) Prelude.. Lens.mapping Prelude._Coerce

-- | The response's http status code.
listTableMetadataResponse_httpStatus :: Lens.Lens' ListTableMetadataResponse Prelude.Int
listTableMetadataResponse_httpStatus = Lens.lens (\ListTableMetadataResponse' {httpStatus} -> httpStatus) (\s@ListTableMetadataResponse' {} a -> s {httpStatus = a} :: ListTableMetadataResponse)

instance Prelude.NFData ListTableMetadataResponse
