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
-- Module      : Amazonka.Transcribe.ListTranscriptionJobs
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
--
-- Lists transcription jobs with the specified status.
module Amazonka.Transcribe.ListTranscriptionJobs
  ( -- * Creating a Request
    ListTranscriptionJobs (..),
    newListTranscriptionJobs,

    -- * Request Lenses
    listTranscriptionJobs_nextToken,
    listTranscriptionJobs_status,
    listTranscriptionJobs_maxResults,
    listTranscriptionJobs_jobNameContains,

    -- * Destructuring the Response
    ListTranscriptionJobsResponse (..),
    newListTranscriptionJobsResponse,

    -- * Response Lenses
    listTranscriptionJobsResponse_nextToken,
    listTranscriptionJobsResponse_transcriptionJobSummaries,
    listTranscriptionJobsResponse_status,
    listTranscriptionJobsResponse_httpStatus,
  )
where

import qualified Amazonka.Core as Core
import qualified Amazonka.Lens as Lens
import qualified Amazonka.Prelude as Prelude
import qualified Amazonka.Request as Request
import qualified Amazonka.Response as Response
import Amazonka.Transcribe.Types

-- | /See:/ 'newListTranscriptionJobs' smart constructor.
data ListTranscriptionJobs = ListTranscriptionJobs'
  { -- | If the result of the previous request to @ListTranscriptionJobs@ is
    -- truncated, include the @NextToken@ to fetch the next set of jobs.
    nextToken :: Prelude.Maybe Prelude.Text,
    -- | When specified, returns only transcription jobs with the specified
    -- status. Jobs are ordered by creation date, with the newest jobs returned
    -- first. If you don’t specify a status, Amazon Transcribe returns all
    -- transcription jobs ordered by creation date.
    status :: Prelude.Maybe TranscriptionJobStatus,
    -- | The maximum number of jobs to return in each page of results. If there
    -- are fewer results than the value you specify, only the actual results
    -- are returned. If you do not specify a value, the default of 5 is used.
    maxResults :: Prelude.Maybe Prelude.Natural,
    -- | When specified, the jobs returned in the list are limited to jobs whose
    -- name contains the specified string.
    jobNameContains :: Prelude.Maybe Prelude.Text
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'ListTranscriptionJobs' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'nextToken', 'listTranscriptionJobs_nextToken' - If the result of the previous request to @ListTranscriptionJobs@ is
-- truncated, include the @NextToken@ to fetch the next set of jobs.
--
-- 'status', 'listTranscriptionJobs_status' - When specified, returns only transcription jobs with the specified
-- status. Jobs are ordered by creation date, with the newest jobs returned
-- first. If you don’t specify a status, Amazon Transcribe returns all
-- transcription jobs ordered by creation date.
--
-- 'maxResults', 'listTranscriptionJobs_maxResults' - The maximum number of jobs to return in each page of results. If there
-- are fewer results than the value you specify, only the actual results
-- are returned. If you do not specify a value, the default of 5 is used.
--
-- 'jobNameContains', 'listTranscriptionJobs_jobNameContains' - When specified, the jobs returned in the list are limited to jobs whose
-- name contains the specified string.
newListTranscriptionJobs ::
  ListTranscriptionJobs
newListTranscriptionJobs =
  ListTranscriptionJobs'
    { nextToken = Prelude.Nothing,
      status = Prelude.Nothing,
      maxResults = Prelude.Nothing,
      jobNameContains = Prelude.Nothing
    }

-- | If the result of the previous request to @ListTranscriptionJobs@ is
-- truncated, include the @NextToken@ to fetch the next set of jobs.
listTranscriptionJobs_nextToken :: Lens.Lens' ListTranscriptionJobs (Prelude.Maybe Prelude.Text)
listTranscriptionJobs_nextToken = Lens.lens (\ListTranscriptionJobs' {nextToken} -> nextToken) (\s@ListTranscriptionJobs' {} a -> s {nextToken = a} :: ListTranscriptionJobs)

-- | When specified, returns only transcription jobs with the specified
-- status. Jobs are ordered by creation date, with the newest jobs returned
-- first. If you don’t specify a status, Amazon Transcribe returns all
-- transcription jobs ordered by creation date.
listTranscriptionJobs_status :: Lens.Lens' ListTranscriptionJobs (Prelude.Maybe TranscriptionJobStatus)
listTranscriptionJobs_status = Lens.lens (\ListTranscriptionJobs' {status} -> status) (\s@ListTranscriptionJobs' {} a -> s {status = a} :: ListTranscriptionJobs)

-- | The maximum number of jobs to return in each page of results. If there
-- are fewer results than the value you specify, only the actual results
-- are returned. If you do not specify a value, the default of 5 is used.
listTranscriptionJobs_maxResults :: Lens.Lens' ListTranscriptionJobs (Prelude.Maybe Prelude.Natural)
listTranscriptionJobs_maxResults = Lens.lens (\ListTranscriptionJobs' {maxResults} -> maxResults) (\s@ListTranscriptionJobs' {} a -> s {maxResults = a} :: ListTranscriptionJobs)

-- | When specified, the jobs returned in the list are limited to jobs whose
-- name contains the specified string.
listTranscriptionJobs_jobNameContains :: Lens.Lens' ListTranscriptionJobs (Prelude.Maybe Prelude.Text)
listTranscriptionJobs_jobNameContains = Lens.lens (\ListTranscriptionJobs' {jobNameContains} -> jobNameContains) (\s@ListTranscriptionJobs' {} a -> s {jobNameContains = a} :: ListTranscriptionJobs)

instance Core.AWSRequest ListTranscriptionJobs where
  type
    AWSResponse ListTranscriptionJobs =
      ListTranscriptionJobsResponse
  request = Request.postJSON defaultService
  response =
    Response.receiveJSON
      ( \s h x ->
          ListTranscriptionJobsResponse'
            Prelude.<$> (x Core..?> "NextToken")
            Prelude.<*> ( x Core..?> "TranscriptionJobSummaries"
                            Core..!@ Prelude.mempty
                        )
            Prelude.<*> (x Core..?> "Status")
            Prelude.<*> (Prelude.pure (Prelude.fromEnum s))
      )

instance Prelude.Hashable ListTranscriptionJobs where
  hashWithSalt _salt ListTranscriptionJobs' {..} =
    _salt `Prelude.hashWithSalt` nextToken
      `Prelude.hashWithSalt` status
      `Prelude.hashWithSalt` maxResults
      `Prelude.hashWithSalt` jobNameContains

instance Prelude.NFData ListTranscriptionJobs where
  rnf ListTranscriptionJobs' {..} =
    Prelude.rnf nextToken
      `Prelude.seq` Prelude.rnf status
      `Prelude.seq` Prelude.rnf maxResults
      `Prelude.seq` Prelude.rnf jobNameContains

instance Core.ToHeaders ListTranscriptionJobs where
  toHeaders =
    Prelude.const
      ( Prelude.mconcat
          [ "X-Amz-Target"
              Core.=# ( "Transcribe.ListTranscriptionJobs" ::
                          Prelude.ByteString
                      ),
            "Content-Type"
              Core.=# ( "application/x-amz-json-1.1" ::
                          Prelude.ByteString
                      )
          ]
      )

instance Core.ToJSON ListTranscriptionJobs where
  toJSON ListTranscriptionJobs' {..} =
    Core.object
      ( Prelude.catMaybes
          [ ("NextToken" Core..=) Prelude.<$> nextToken,
            ("Status" Core..=) Prelude.<$> status,
            ("MaxResults" Core..=) Prelude.<$> maxResults,
            ("JobNameContains" Core..=)
              Prelude.<$> jobNameContains
          ]
      )

instance Core.ToPath ListTranscriptionJobs where
  toPath = Prelude.const "/"

instance Core.ToQuery ListTranscriptionJobs where
  toQuery = Prelude.const Prelude.mempty

-- | /See:/ 'newListTranscriptionJobsResponse' smart constructor.
data ListTranscriptionJobsResponse = ListTranscriptionJobsResponse'
  { -- | The @ListTranscriptionJobs@ operation returns a page of jobs at a time.
    -- The maximum size of the page is set by the @MaxResults@ parameter. If
    -- there are more jobs in the list than the page size, Amazon Transcribe
    -- returns the @NextPage@ token. Include the token in the next request to
    -- the @ListTranscriptionJobs@ operation to return in the next page of
    -- jobs.
    nextToken :: Prelude.Maybe Prelude.Text,
    -- | A list of objects containing summary information for a transcription
    -- job.
    transcriptionJobSummaries :: Prelude.Maybe [TranscriptionJobSummary],
    -- | The requested status of the jobs returned.
    status :: Prelude.Maybe TranscriptionJobStatus,
    -- | The response's http status code.
    httpStatus :: Prelude.Int
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'ListTranscriptionJobsResponse' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'nextToken', 'listTranscriptionJobsResponse_nextToken' - The @ListTranscriptionJobs@ operation returns a page of jobs at a time.
-- The maximum size of the page is set by the @MaxResults@ parameter. If
-- there are more jobs in the list than the page size, Amazon Transcribe
-- returns the @NextPage@ token. Include the token in the next request to
-- the @ListTranscriptionJobs@ operation to return in the next page of
-- jobs.
--
-- 'transcriptionJobSummaries', 'listTranscriptionJobsResponse_transcriptionJobSummaries' - A list of objects containing summary information for a transcription
-- job.
--
-- 'status', 'listTranscriptionJobsResponse_status' - The requested status of the jobs returned.
--
-- 'httpStatus', 'listTranscriptionJobsResponse_httpStatus' - The response's http status code.
newListTranscriptionJobsResponse ::
  -- | 'httpStatus'
  Prelude.Int ->
  ListTranscriptionJobsResponse
newListTranscriptionJobsResponse pHttpStatus_ =
  ListTranscriptionJobsResponse'
    { nextToken =
        Prelude.Nothing,
      transcriptionJobSummaries = Prelude.Nothing,
      status = Prelude.Nothing,
      httpStatus = pHttpStatus_
    }

-- | The @ListTranscriptionJobs@ operation returns a page of jobs at a time.
-- The maximum size of the page is set by the @MaxResults@ parameter. If
-- there are more jobs in the list than the page size, Amazon Transcribe
-- returns the @NextPage@ token. Include the token in the next request to
-- the @ListTranscriptionJobs@ operation to return in the next page of
-- jobs.
listTranscriptionJobsResponse_nextToken :: Lens.Lens' ListTranscriptionJobsResponse (Prelude.Maybe Prelude.Text)
listTranscriptionJobsResponse_nextToken = Lens.lens (\ListTranscriptionJobsResponse' {nextToken} -> nextToken) (\s@ListTranscriptionJobsResponse' {} a -> s {nextToken = a} :: ListTranscriptionJobsResponse)

-- | A list of objects containing summary information for a transcription
-- job.
listTranscriptionJobsResponse_transcriptionJobSummaries :: Lens.Lens' ListTranscriptionJobsResponse (Prelude.Maybe [TranscriptionJobSummary])
listTranscriptionJobsResponse_transcriptionJobSummaries = Lens.lens (\ListTranscriptionJobsResponse' {transcriptionJobSummaries} -> transcriptionJobSummaries) (\s@ListTranscriptionJobsResponse' {} a -> s {transcriptionJobSummaries = a} :: ListTranscriptionJobsResponse) Prelude.. Lens.mapping Lens.coerced

-- | The requested status of the jobs returned.
listTranscriptionJobsResponse_status :: Lens.Lens' ListTranscriptionJobsResponse (Prelude.Maybe TranscriptionJobStatus)
listTranscriptionJobsResponse_status = Lens.lens (\ListTranscriptionJobsResponse' {status} -> status) (\s@ListTranscriptionJobsResponse' {} a -> s {status = a} :: ListTranscriptionJobsResponse)

-- | The response's http status code.
listTranscriptionJobsResponse_httpStatus :: Lens.Lens' ListTranscriptionJobsResponse Prelude.Int
listTranscriptionJobsResponse_httpStatus = Lens.lens (\ListTranscriptionJobsResponse' {httpStatus} -> httpStatus) (\s@ListTranscriptionJobsResponse' {} a -> s {httpStatus = a} :: ListTranscriptionJobsResponse)

instance Prelude.NFData ListTranscriptionJobsResponse where
  rnf ListTranscriptionJobsResponse' {..} =
    Prelude.rnf nextToken
      `Prelude.seq` Prelude.rnf transcriptionJobSummaries
      `Prelude.seq` Prelude.rnf status
      `Prelude.seq` Prelude.rnf httpStatus
