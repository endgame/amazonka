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
-- Module      : Amazonka.ChimeSDKMessaging.Types.ChannelMessageCallback
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Amazonka.ChimeSDKMessaging.Types.ChannelMessageCallback where

import qualified Amazonka.Core as Core
import qualified Amazonka.Lens as Lens
import qualified Amazonka.Prelude as Prelude

-- | Stores information about a callback.
--
-- /See:/ 'newChannelMessageCallback' smart constructor.
data ChannelMessageCallback = ChannelMessageCallback'
  { -- | The message metadata.
    metadata :: Prelude.Maybe (Core.Sensitive Prelude.Text),
    -- | The message content.
    content :: Prelude.Maybe (Core.Sensitive Prelude.Text),
    -- | The message ID.
    messageId :: Prelude.Text
  }
  deriving (Prelude.Eq, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'ChannelMessageCallback' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'metadata', 'channelMessageCallback_metadata' - The message metadata.
--
-- 'content', 'channelMessageCallback_content' - The message content.
--
-- 'messageId', 'channelMessageCallback_messageId' - The message ID.
newChannelMessageCallback ::
  -- | 'messageId'
  Prelude.Text ->
  ChannelMessageCallback
newChannelMessageCallback pMessageId_ =
  ChannelMessageCallback'
    { metadata = Prelude.Nothing,
      content = Prelude.Nothing,
      messageId = pMessageId_
    }

-- | The message metadata.
channelMessageCallback_metadata :: Lens.Lens' ChannelMessageCallback (Prelude.Maybe Prelude.Text)
channelMessageCallback_metadata = Lens.lens (\ChannelMessageCallback' {metadata} -> metadata) (\s@ChannelMessageCallback' {} a -> s {metadata = a} :: ChannelMessageCallback) Prelude.. Lens.mapping Core._Sensitive

-- | The message content.
channelMessageCallback_content :: Lens.Lens' ChannelMessageCallback (Prelude.Maybe Prelude.Text)
channelMessageCallback_content = Lens.lens (\ChannelMessageCallback' {content} -> content) (\s@ChannelMessageCallback' {} a -> s {content = a} :: ChannelMessageCallback) Prelude.. Lens.mapping Core._Sensitive

-- | The message ID.
channelMessageCallback_messageId :: Lens.Lens' ChannelMessageCallback Prelude.Text
channelMessageCallback_messageId = Lens.lens (\ChannelMessageCallback' {messageId} -> messageId) (\s@ChannelMessageCallback' {} a -> s {messageId = a} :: ChannelMessageCallback)

instance Prelude.Hashable ChannelMessageCallback where
  hashWithSalt _salt ChannelMessageCallback' {..} =
    _salt `Prelude.hashWithSalt` metadata
      `Prelude.hashWithSalt` content
      `Prelude.hashWithSalt` messageId

instance Prelude.NFData ChannelMessageCallback where
  rnf ChannelMessageCallback' {..} =
    Prelude.rnf metadata
      `Prelude.seq` Prelude.rnf content
      `Prelude.seq` Prelude.rnf messageId

instance Core.ToJSON ChannelMessageCallback where
  toJSON ChannelMessageCallback' {..} =
    Core.object
      ( Prelude.catMaybes
          [ ("Metadata" Core..=) Prelude.<$> metadata,
            ("Content" Core..=) Prelude.<$> content,
            Prelude.Just ("MessageId" Core..= messageId)
          ]
      )
