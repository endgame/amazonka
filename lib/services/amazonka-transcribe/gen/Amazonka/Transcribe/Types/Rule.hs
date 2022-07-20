{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

-- Derived from AWS service descriptions, licensed under Apache 2.0.

-- |
-- Module      : Amazonka.Transcribe.Types.Rule
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Amazonka.Transcribe.Types.Rule where

import qualified Amazonka.Core as Core
import qualified Amazonka.Lens as Lens
import qualified Amazonka.Prelude as Prelude
import Amazonka.Transcribe.Types.InterruptionFilter
import Amazonka.Transcribe.Types.NonTalkTimeFilter
import Amazonka.Transcribe.Types.SentimentFilter
import Amazonka.Transcribe.Types.TranscriptFilter

-- | A condition in the call between the customer and the agent that you want
-- to filter for.
--
-- /See:/ 'newRule' smart constructor.
data Rule = Rule'
  { -- | A condition that catches particular words or phrases based on a exact
    -- match. For example, if you set the phrase \"I want to speak to the
    -- manager\", only that exact phrase will be returned.
    transcriptFilter :: Prelude.Maybe TranscriptFilter,
    -- | A condition for a time period when either the customer or agent was
    -- interrupting the other person.
    interruptionFilter :: Prelude.Maybe InterruptionFilter,
    -- | A condition that is applied to a particular customer sentiment.
    sentimentFilter :: Prelude.Maybe SentimentFilter,
    -- | A condition for a time period when neither the customer nor the agent
    -- was talking.
    nonTalkTimeFilter :: Prelude.Maybe NonTalkTimeFilter
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'Rule' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'transcriptFilter', 'rule_transcriptFilter' - A condition that catches particular words or phrases based on a exact
-- match. For example, if you set the phrase \"I want to speak to the
-- manager\", only that exact phrase will be returned.
--
-- 'interruptionFilter', 'rule_interruptionFilter' - A condition for a time period when either the customer or agent was
-- interrupting the other person.
--
-- 'sentimentFilter', 'rule_sentimentFilter' - A condition that is applied to a particular customer sentiment.
--
-- 'nonTalkTimeFilter', 'rule_nonTalkTimeFilter' - A condition for a time period when neither the customer nor the agent
-- was talking.
newRule ::
  Rule
newRule =
  Rule'
    { transcriptFilter = Prelude.Nothing,
      interruptionFilter = Prelude.Nothing,
      sentimentFilter = Prelude.Nothing,
      nonTalkTimeFilter = Prelude.Nothing
    }

-- | A condition that catches particular words or phrases based on a exact
-- match. For example, if you set the phrase \"I want to speak to the
-- manager\", only that exact phrase will be returned.
rule_transcriptFilter :: Lens.Lens' Rule (Prelude.Maybe TranscriptFilter)
rule_transcriptFilter = Lens.lens (\Rule' {transcriptFilter} -> transcriptFilter) (\s@Rule' {} a -> s {transcriptFilter = a} :: Rule)

-- | A condition for a time period when either the customer or agent was
-- interrupting the other person.
rule_interruptionFilter :: Lens.Lens' Rule (Prelude.Maybe InterruptionFilter)
rule_interruptionFilter = Lens.lens (\Rule' {interruptionFilter} -> interruptionFilter) (\s@Rule' {} a -> s {interruptionFilter = a} :: Rule)

-- | A condition that is applied to a particular customer sentiment.
rule_sentimentFilter :: Lens.Lens' Rule (Prelude.Maybe SentimentFilter)
rule_sentimentFilter = Lens.lens (\Rule' {sentimentFilter} -> sentimentFilter) (\s@Rule' {} a -> s {sentimentFilter = a} :: Rule)

-- | A condition for a time period when neither the customer nor the agent
-- was talking.
rule_nonTalkTimeFilter :: Lens.Lens' Rule (Prelude.Maybe NonTalkTimeFilter)
rule_nonTalkTimeFilter = Lens.lens (\Rule' {nonTalkTimeFilter} -> nonTalkTimeFilter) (\s@Rule' {} a -> s {nonTalkTimeFilter = a} :: Rule)

instance Core.FromJSON Rule where
  parseJSON =
    Core.withObject
      "Rule"
      ( \x ->
          Rule'
            Prelude.<$> (x Core..:? "TranscriptFilter")
            Prelude.<*> (x Core..:? "InterruptionFilter")
            Prelude.<*> (x Core..:? "SentimentFilter")
            Prelude.<*> (x Core..:? "NonTalkTimeFilter")
      )

instance Prelude.Hashable Rule where
  hashWithSalt _salt Rule' {..} =
    _salt `Prelude.hashWithSalt` transcriptFilter
      `Prelude.hashWithSalt` interruptionFilter
      `Prelude.hashWithSalt` sentimentFilter
      `Prelude.hashWithSalt` nonTalkTimeFilter

instance Prelude.NFData Rule where
  rnf Rule' {..} =
    Prelude.rnf transcriptFilter
      `Prelude.seq` Prelude.rnf interruptionFilter
      `Prelude.seq` Prelude.rnf sentimentFilter
      `Prelude.seq` Prelude.rnf nonTalkTimeFilter

instance Core.ToJSON Rule where
  toJSON Rule' {..} =
    Core.object
      ( Prelude.catMaybes
          [ ("TranscriptFilter" Core..=)
              Prelude.<$> transcriptFilter,
            ("InterruptionFilter" Core..=)
              Prelude.<$> interruptionFilter,
            ("SentimentFilter" Core..=)
              Prelude.<$> sentimentFilter,
            ("NonTalkTimeFilter" Core..=)
              Prelude.<$> nonTalkTimeFilter
          ]
      )
