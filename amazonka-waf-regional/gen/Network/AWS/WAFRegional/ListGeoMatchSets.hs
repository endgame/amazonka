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
-- Module      : Network.AWS.WAFRegional.ListGeoMatchSets
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
--
-- This is __AWS WAF Classic__ documentation. For more information, see
-- <https://docs.aws.amazon.com/waf/latest/developerguide/classic-waf-chapter.html AWS WAF Classic>
-- in the developer guide.
--
-- __For the latest version of AWS WAF__, use the AWS WAFV2 API and see the
-- <https://docs.aws.amazon.com/waf/latest/developerguide/waf-chapter.html AWS WAF Developer Guide>.
-- With the latest version, AWS WAF has a single set of endpoints for
-- regional and global use.
--
-- Returns an array of GeoMatchSetSummary objects in the response.
module Network.AWS.WAFRegional.ListGeoMatchSets
  ( -- * Creating a Request
    ListGeoMatchSets (..),
    newListGeoMatchSets,

    -- * Request Lenses
    listGeoMatchSets_nextMarker,
    listGeoMatchSets_limit,

    -- * Destructuring the Response
    ListGeoMatchSetsResponse (..),
    newListGeoMatchSetsResponse,

    -- * Response Lenses
    listGeoMatchSetsResponse_geoMatchSets,
    listGeoMatchSetsResponse_nextMarker,
    listGeoMatchSetsResponse_httpStatus,
  )
where

import qualified Network.AWS.Lens as Lens
import qualified Network.AWS.Prelude as Prelude
import qualified Network.AWS.Request as Request
import qualified Network.AWS.Response as Response
import Network.AWS.WAFRegional.Types

-- | /See:/ 'newListGeoMatchSets' smart constructor.
data ListGeoMatchSets = ListGeoMatchSets'
  { -- | If you specify a value for @Limit@ and you have more @GeoMatchSet@s than
    -- the value of @Limit@, AWS WAF returns a @NextMarker@ value in the
    -- response that allows you to list another group of @GeoMatchSet@ objects.
    -- For the second and subsequent @ListGeoMatchSets@ requests, specify the
    -- value of @NextMarker@ from the previous response to get information
    -- about another batch of @GeoMatchSet@ objects.
    nextMarker :: Prelude.Maybe Prelude.Text,
    -- | Specifies the number of @GeoMatchSet@ objects that you want AWS WAF to
    -- return for this request. If you have more @GeoMatchSet@ objects than the
    -- number you specify for @Limit@, the response includes a @NextMarker@
    -- value that you can use to get another batch of @GeoMatchSet@ objects.
    limit :: Prelude.Maybe Prelude.Natural
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Data, Prelude.Typeable, Prelude.Generic)

-- |
-- Create a value of 'ListGeoMatchSets' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'nextMarker', 'listGeoMatchSets_nextMarker' - If you specify a value for @Limit@ and you have more @GeoMatchSet@s than
-- the value of @Limit@, AWS WAF returns a @NextMarker@ value in the
-- response that allows you to list another group of @GeoMatchSet@ objects.
-- For the second and subsequent @ListGeoMatchSets@ requests, specify the
-- value of @NextMarker@ from the previous response to get information
-- about another batch of @GeoMatchSet@ objects.
--
-- 'limit', 'listGeoMatchSets_limit' - Specifies the number of @GeoMatchSet@ objects that you want AWS WAF to
-- return for this request. If you have more @GeoMatchSet@ objects than the
-- number you specify for @Limit@, the response includes a @NextMarker@
-- value that you can use to get another batch of @GeoMatchSet@ objects.
newListGeoMatchSets ::
  ListGeoMatchSets
newListGeoMatchSets =
  ListGeoMatchSets'
    { nextMarker = Prelude.Nothing,
      limit = Prelude.Nothing
    }

-- | If you specify a value for @Limit@ and you have more @GeoMatchSet@s than
-- the value of @Limit@, AWS WAF returns a @NextMarker@ value in the
-- response that allows you to list another group of @GeoMatchSet@ objects.
-- For the second and subsequent @ListGeoMatchSets@ requests, specify the
-- value of @NextMarker@ from the previous response to get information
-- about another batch of @GeoMatchSet@ objects.
listGeoMatchSets_nextMarker :: Lens.Lens' ListGeoMatchSets (Prelude.Maybe Prelude.Text)
listGeoMatchSets_nextMarker = Lens.lens (\ListGeoMatchSets' {nextMarker} -> nextMarker) (\s@ListGeoMatchSets' {} a -> s {nextMarker = a} :: ListGeoMatchSets)

-- | Specifies the number of @GeoMatchSet@ objects that you want AWS WAF to
-- return for this request. If you have more @GeoMatchSet@ objects than the
-- number you specify for @Limit@, the response includes a @NextMarker@
-- value that you can use to get another batch of @GeoMatchSet@ objects.
listGeoMatchSets_limit :: Lens.Lens' ListGeoMatchSets (Prelude.Maybe Prelude.Natural)
listGeoMatchSets_limit = Lens.lens (\ListGeoMatchSets' {limit} -> limit) (\s@ListGeoMatchSets' {} a -> s {limit = a} :: ListGeoMatchSets)

instance Prelude.AWSRequest ListGeoMatchSets where
  type Rs ListGeoMatchSets = ListGeoMatchSetsResponse
  request = Request.postJSON defaultService
  response =
    Response.receiveJSON
      ( \s h x ->
          ListGeoMatchSetsResponse'
            Prelude.<$> ( x Prelude..?> "GeoMatchSets"
                            Prelude..!@ Prelude.mempty
                        )
            Prelude.<*> (x Prelude..?> "NextMarker")
            Prelude.<*> (Prelude.pure (Prelude.fromEnum s))
      )

instance Prelude.Hashable ListGeoMatchSets

instance Prelude.NFData ListGeoMatchSets

instance Prelude.ToHeaders ListGeoMatchSets where
  toHeaders =
    Prelude.const
      ( Prelude.mconcat
          [ "X-Amz-Target"
              Prelude.=# ( "AWSWAF_Regional_20161128.ListGeoMatchSets" ::
                             Prelude.ByteString
                         ),
            "Content-Type"
              Prelude.=# ( "application/x-amz-json-1.1" ::
                             Prelude.ByteString
                         )
          ]
      )

instance Prelude.ToJSON ListGeoMatchSets where
  toJSON ListGeoMatchSets' {..} =
    Prelude.object
      ( Prelude.catMaybes
          [ ("NextMarker" Prelude..=) Prelude.<$> nextMarker,
            ("Limit" Prelude..=) Prelude.<$> limit
          ]
      )

instance Prelude.ToPath ListGeoMatchSets where
  toPath = Prelude.const "/"

instance Prelude.ToQuery ListGeoMatchSets where
  toQuery = Prelude.const Prelude.mempty

-- | /See:/ 'newListGeoMatchSetsResponse' smart constructor.
data ListGeoMatchSetsResponse = ListGeoMatchSetsResponse'
  { -- | An array of GeoMatchSetSummary objects.
    geoMatchSets :: Prelude.Maybe [GeoMatchSetSummary],
    -- | If you have more @GeoMatchSet@ objects than the number that you
    -- specified for @Limit@ in the request, the response includes a
    -- @NextMarker@ value. To list more @GeoMatchSet@ objects, submit another
    -- @ListGeoMatchSets@ request, and specify the @NextMarker@ value from the
    -- response in the @NextMarker@ value in the next request.
    nextMarker :: Prelude.Maybe Prelude.Text,
    -- | The response's http status code.
    httpStatus :: Prelude.Int
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Data, Prelude.Typeable, Prelude.Generic)

-- |
-- Create a value of 'ListGeoMatchSetsResponse' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'geoMatchSets', 'listGeoMatchSetsResponse_geoMatchSets' - An array of GeoMatchSetSummary objects.
--
-- 'nextMarker', 'listGeoMatchSetsResponse_nextMarker' - If you have more @GeoMatchSet@ objects than the number that you
-- specified for @Limit@ in the request, the response includes a
-- @NextMarker@ value. To list more @GeoMatchSet@ objects, submit another
-- @ListGeoMatchSets@ request, and specify the @NextMarker@ value from the
-- response in the @NextMarker@ value in the next request.
--
-- 'httpStatus', 'listGeoMatchSetsResponse_httpStatus' - The response's http status code.
newListGeoMatchSetsResponse ::
  -- | 'httpStatus'
  Prelude.Int ->
  ListGeoMatchSetsResponse
newListGeoMatchSetsResponse pHttpStatus_ =
  ListGeoMatchSetsResponse'
    { geoMatchSets =
        Prelude.Nothing,
      nextMarker = Prelude.Nothing,
      httpStatus = pHttpStatus_
    }

-- | An array of GeoMatchSetSummary objects.
listGeoMatchSetsResponse_geoMatchSets :: Lens.Lens' ListGeoMatchSetsResponse (Prelude.Maybe [GeoMatchSetSummary])
listGeoMatchSetsResponse_geoMatchSets = Lens.lens (\ListGeoMatchSetsResponse' {geoMatchSets} -> geoMatchSets) (\s@ListGeoMatchSetsResponse' {} a -> s {geoMatchSets = a} :: ListGeoMatchSetsResponse) Prelude.. Lens.mapping Prelude._Coerce

-- | If you have more @GeoMatchSet@ objects than the number that you
-- specified for @Limit@ in the request, the response includes a
-- @NextMarker@ value. To list more @GeoMatchSet@ objects, submit another
-- @ListGeoMatchSets@ request, and specify the @NextMarker@ value from the
-- response in the @NextMarker@ value in the next request.
listGeoMatchSetsResponse_nextMarker :: Lens.Lens' ListGeoMatchSetsResponse (Prelude.Maybe Prelude.Text)
listGeoMatchSetsResponse_nextMarker = Lens.lens (\ListGeoMatchSetsResponse' {nextMarker} -> nextMarker) (\s@ListGeoMatchSetsResponse' {} a -> s {nextMarker = a} :: ListGeoMatchSetsResponse)

-- | The response's http status code.
listGeoMatchSetsResponse_httpStatus :: Lens.Lens' ListGeoMatchSetsResponse Prelude.Int
listGeoMatchSetsResponse_httpStatus = Lens.lens (\ListGeoMatchSetsResponse' {httpStatus} -> httpStatus) (\s@ListGeoMatchSetsResponse' {} a -> s {httpStatus = a} :: ListGeoMatchSetsResponse)

instance Prelude.NFData ListGeoMatchSetsResponse
