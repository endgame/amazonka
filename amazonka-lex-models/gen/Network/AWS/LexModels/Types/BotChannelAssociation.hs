{-# LANGUAGE DeriveDataTypeable #-}
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
-- Module      : Network.AWS.LexModels.Types.BotChannelAssociation
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Network.AWS.LexModels.Types.BotChannelAssociation where

import qualified Network.AWS.Lens as Lens
import Network.AWS.LexModels.Types.ChannelStatus
import Network.AWS.LexModels.Types.ChannelType
import qualified Network.AWS.Prelude as Prelude

-- | Represents an association between an Amazon Lex bot and an external
-- messaging platform.
--
-- /See:/ 'newBotChannelAssociation' smart constructor.
data BotChannelAssociation = BotChannelAssociation'
  { -- | An alias pointing to the specific version of the Amazon Lex bot to which
    -- this association is being made.
    botAlias :: Prelude.Maybe Prelude.Text,
    -- | The date that the association between the Amazon Lex bot and the channel
    -- was created.
    createdDate :: Prelude.Maybe Prelude.POSIX,
    -- | The status of the bot channel.
    --
    -- -   @CREATED@ - The channel has been created and is ready for use.
    --
    -- -   @IN_PROGRESS@ - Channel creation is in progress.
    --
    -- -   @FAILED@ - There was an error creating the channel. For information
    --     about the reason for the failure, see the @failureReason@ field.
    status :: Prelude.Maybe ChannelStatus,
    -- | Provides information necessary to communicate with the messaging
    -- platform.
    botConfiguration :: Prelude.Maybe (Prelude.Sensitive (Prelude.HashMap Prelude.Text Prelude.Text)),
    -- | The name of the Amazon Lex bot to which this association is being made.
    --
    -- Currently, Amazon Lex supports associations with Facebook and Slack, and
    -- Twilio.
    botName :: Prelude.Maybe Prelude.Text,
    -- | The name of the association between the bot and the channel.
    name :: Prelude.Maybe Prelude.Text,
    -- | If @status@ is @FAILED@, Amazon Lex provides the reason that it failed
    -- to create the association.
    failureReason :: Prelude.Maybe Prelude.Text,
    -- | A text description of the association you are creating.
    description :: Prelude.Maybe Prelude.Text,
    -- | Specifies the type of association by indicating the type of channel
    -- being established between the Amazon Lex bot and the external messaging
    -- platform.
    type' :: Prelude.Maybe ChannelType
  }
  deriving (Prelude.Eq, Prelude.Show, Prelude.Data, Prelude.Typeable, Prelude.Generic)

-- |
-- Create a value of 'BotChannelAssociation' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'botAlias', 'botChannelAssociation_botAlias' - An alias pointing to the specific version of the Amazon Lex bot to which
-- this association is being made.
--
-- 'createdDate', 'botChannelAssociation_createdDate' - The date that the association between the Amazon Lex bot and the channel
-- was created.
--
-- 'status', 'botChannelAssociation_status' - The status of the bot channel.
--
-- -   @CREATED@ - The channel has been created and is ready for use.
--
-- -   @IN_PROGRESS@ - Channel creation is in progress.
--
-- -   @FAILED@ - There was an error creating the channel. For information
--     about the reason for the failure, see the @failureReason@ field.
--
-- 'botConfiguration', 'botChannelAssociation_botConfiguration' - Provides information necessary to communicate with the messaging
-- platform.
--
-- 'botName', 'botChannelAssociation_botName' - The name of the Amazon Lex bot to which this association is being made.
--
-- Currently, Amazon Lex supports associations with Facebook and Slack, and
-- Twilio.
--
-- 'name', 'botChannelAssociation_name' - The name of the association between the bot and the channel.
--
-- 'failureReason', 'botChannelAssociation_failureReason' - If @status@ is @FAILED@, Amazon Lex provides the reason that it failed
-- to create the association.
--
-- 'description', 'botChannelAssociation_description' - A text description of the association you are creating.
--
-- 'type'', 'botChannelAssociation_type' - Specifies the type of association by indicating the type of channel
-- being established between the Amazon Lex bot and the external messaging
-- platform.
newBotChannelAssociation ::
  BotChannelAssociation
newBotChannelAssociation =
  BotChannelAssociation'
    { botAlias = Prelude.Nothing,
      createdDate = Prelude.Nothing,
      status = Prelude.Nothing,
      botConfiguration = Prelude.Nothing,
      botName = Prelude.Nothing,
      name = Prelude.Nothing,
      failureReason = Prelude.Nothing,
      description = Prelude.Nothing,
      type' = Prelude.Nothing
    }

-- | An alias pointing to the specific version of the Amazon Lex bot to which
-- this association is being made.
botChannelAssociation_botAlias :: Lens.Lens' BotChannelAssociation (Prelude.Maybe Prelude.Text)
botChannelAssociation_botAlias = Lens.lens (\BotChannelAssociation' {botAlias} -> botAlias) (\s@BotChannelAssociation' {} a -> s {botAlias = a} :: BotChannelAssociation)

-- | The date that the association between the Amazon Lex bot and the channel
-- was created.
botChannelAssociation_createdDate :: Lens.Lens' BotChannelAssociation (Prelude.Maybe Prelude.UTCTime)
botChannelAssociation_createdDate = Lens.lens (\BotChannelAssociation' {createdDate} -> createdDate) (\s@BotChannelAssociation' {} a -> s {createdDate = a} :: BotChannelAssociation) Prelude.. Lens.mapping Prelude._Time

-- | The status of the bot channel.
--
-- -   @CREATED@ - The channel has been created and is ready for use.
--
-- -   @IN_PROGRESS@ - Channel creation is in progress.
--
-- -   @FAILED@ - There was an error creating the channel. For information
--     about the reason for the failure, see the @failureReason@ field.
botChannelAssociation_status :: Lens.Lens' BotChannelAssociation (Prelude.Maybe ChannelStatus)
botChannelAssociation_status = Lens.lens (\BotChannelAssociation' {status} -> status) (\s@BotChannelAssociation' {} a -> s {status = a} :: BotChannelAssociation)

-- | Provides information necessary to communicate with the messaging
-- platform.
botChannelAssociation_botConfiguration :: Lens.Lens' BotChannelAssociation (Prelude.Maybe (Prelude.HashMap Prelude.Text Prelude.Text))
botChannelAssociation_botConfiguration = Lens.lens (\BotChannelAssociation' {botConfiguration} -> botConfiguration) (\s@BotChannelAssociation' {} a -> s {botConfiguration = a} :: BotChannelAssociation) Prelude.. Lens.mapping (Prelude._Sensitive Prelude.. Prelude._Coerce)

-- | The name of the Amazon Lex bot to which this association is being made.
--
-- Currently, Amazon Lex supports associations with Facebook and Slack, and
-- Twilio.
botChannelAssociation_botName :: Lens.Lens' BotChannelAssociation (Prelude.Maybe Prelude.Text)
botChannelAssociation_botName = Lens.lens (\BotChannelAssociation' {botName} -> botName) (\s@BotChannelAssociation' {} a -> s {botName = a} :: BotChannelAssociation)

-- | The name of the association between the bot and the channel.
botChannelAssociation_name :: Lens.Lens' BotChannelAssociation (Prelude.Maybe Prelude.Text)
botChannelAssociation_name = Lens.lens (\BotChannelAssociation' {name} -> name) (\s@BotChannelAssociation' {} a -> s {name = a} :: BotChannelAssociation)

-- | If @status@ is @FAILED@, Amazon Lex provides the reason that it failed
-- to create the association.
botChannelAssociation_failureReason :: Lens.Lens' BotChannelAssociation (Prelude.Maybe Prelude.Text)
botChannelAssociation_failureReason = Lens.lens (\BotChannelAssociation' {failureReason} -> failureReason) (\s@BotChannelAssociation' {} a -> s {failureReason = a} :: BotChannelAssociation)

-- | A text description of the association you are creating.
botChannelAssociation_description :: Lens.Lens' BotChannelAssociation (Prelude.Maybe Prelude.Text)
botChannelAssociation_description = Lens.lens (\BotChannelAssociation' {description} -> description) (\s@BotChannelAssociation' {} a -> s {description = a} :: BotChannelAssociation)

-- | Specifies the type of association by indicating the type of channel
-- being established between the Amazon Lex bot and the external messaging
-- platform.
botChannelAssociation_type :: Lens.Lens' BotChannelAssociation (Prelude.Maybe ChannelType)
botChannelAssociation_type = Lens.lens (\BotChannelAssociation' {type'} -> type') (\s@BotChannelAssociation' {} a -> s {type' = a} :: BotChannelAssociation)

instance Prelude.FromJSON BotChannelAssociation where
  parseJSON =
    Prelude.withObject
      "BotChannelAssociation"
      ( \x ->
          BotChannelAssociation'
            Prelude.<$> (x Prelude..:? "botAlias")
            Prelude.<*> (x Prelude..:? "createdDate")
            Prelude.<*> (x Prelude..:? "status")
            Prelude.<*> ( x Prelude..:? "botConfiguration"
                            Prelude..!= Prelude.mempty
                        )
            Prelude.<*> (x Prelude..:? "botName")
            Prelude.<*> (x Prelude..:? "name")
            Prelude.<*> (x Prelude..:? "failureReason")
            Prelude.<*> (x Prelude..:? "description")
            Prelude.<*> (x Prelude..:? "type")
      )

instance Prelude.Hashable BotChannelAssociation

instance Prelude.NFData BotChannelAssociation
