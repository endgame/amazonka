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
-- Module      : Amazonka.SQS.Types.Message
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Amazonka.SQS.Types.Message where

import qualified Amazonka.Core as Core
import qualified Amazonka.Lens as Lens
import qualified Amazonka.Prelude as Prelude
import Amazonka.SQS.Types.MessageAttribute
import Amazonka.SQS.Types.MessageAttributeValue

-- | An Amazon SQS message.
--
-- /See:/ 'newMessage' smart constructor.
data Message = Message'
  { -- | An identifier associated with the act of receiving the message. A new
    -- receipt handle is returned every time you receive a message. When
    -- deleting a message, you provide the last received receipt handle to
    -- delete the message.
    receiptHandle :: Prelude.Maybe Prelude.Text,
    -- | The message\'s contents (not URL-encoded).
    body :: Prelude.Maybe Prelude.Text,
    -- | A unique identifier for the message. A @MessageId@is considered unique
    -- across all accounts for an extended period of time.
    messageId :: Prelude.Maybe Prelude.Text,
    -- | Each message attribute consists of a @Name@, @Type@, and @Value@. For
    -- more information, see
    -- <https://docs.aws.amazon.com/AWSSimpleQueueService/latest/SQSDeveloperGuide/sqs-message-metadata.html#sqs-message-attributes Amazon SQS message attributes>
    -- in the /Amazon SQS Developer Guide/.
    messageAttributes :: Prelude.Maybe (Prelude.HashMap Prelude.Text MessageAttributeValue),
    -- | A map of the attributes requested in @ ReceiveMessage @ to their
    -- respective values. Supported attributes:
    --
    -- -   @ApproximateReceiveCount@
    --
    -- -   @ApproximateFirstReceiveTimestamp@
    --
    -- -   @MessageDeduplicationId@
    --
    -- -   @MessageGroupId@
    --
    -- -   @SenderId@
    --
    -- -   @SentTimestamp@
    --
    -- -   @SequenceNumber@
    --
    -- @ApproximateFirstReceiveTimestamp@ and @SentTimestamp@ are each returned
    -- as an integer representing the
    -- <http://en.wikipedia.org/wiki/Unix_time epoch time> in milliseconds.
    attributes :: Prelude.Maybe (Prelude.HashMap MessageAttribute Prelude.Text),
    -- | An MD5 digest of the non-URL-encoded message body string.
    mD5OfBody :: Prelude.Maybe Prelude.Text,
    -- | An MD5 digest of the non-URL-encoded message attribute string. You can
    -- use this attribute to verify that Amazon SQS received the message
    -- correctly. Amazon SQS URL-decodes the message before creating the MD5
    -- digest. For information about MD5, see
    -- <https://www.ietf.org/rfc/rfc1321.txt RFC1321>.
    mD5OfMessageAttributes :: Prelude.Maybe Prelude.Text
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'Message' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'receiptHandle', 'message_receiptHandle' - An identifier associated with the act of receiving the message. A new
-- receipt handle is returned every time you receive a message. When
-- deleting a message, you provide the last received receipt handle to
-- delete the message.
--
-- 'body', 'message_body' - The message\'s contents (not URL-encoded).
--
-- 'messageId', 'message_messageId' - A unique identifier for the message. A @MessageId@is considered unique
-- across all accounts for an extended period of time.
--
-- 'messageAttributes', 'message_messageAttributes' - Each message attribute consists of a @Name@, @Type@, and @Value@. For
-- more information, see
-- <https://docs.aws.amazon.com/AWSSimpleQueueService/latest/SQSDeveloperGuide/sqs-message-metadata.html#sqs-message-attributes Amazon SQS message attributes>
-- in the /Amazon SQS Developer Guide/.
--
-- 'attributes', 'message_attributes' - A map of the attributes requested in @ ReceiveMessage @ to their
-- respective values. Supported attributes:
--
-- -   @ApproximateReceiveCount@
--
-- -   @ApproximateFirstReceiveTimestamp@
--
-- -   @MessageDeduplicationId@
--
-- -   @MessageGroupId@
--
-- -   @SenderId@
--
-- -   @SentTimestamp@
--
-- -   @SequenceNumber@
--
-- @ApproximateFirstReceiveTimestamp@ and @SentTimestamp@ are each returned
-- as an integer representing the
-- <http://en.wikipedia.org/wiki/Unix_time epoch time> in milliseconds.
--
-- 'mD5OfBody', 'message_mD5OfBody' - An MD5 digest of the non-URL-encoded message body string.
--
-- 'mD5OfMessageAttributes', 'message_mD5OfMessageAttributes' - An MD5 digest of the non-URL-encoded message attribute string. You can
-- use this attribute to verify that Amazon SQS received the message
-- correctly. Amazon SQS URL-decodes the message before creating the MD5
-- digest. For information about MD5, see
-- <https://www.ietf.org/rfc/rfc1321.txt RFC1321>.
newMessage ::
  Message
newMessage =
  Message'
    { receiptHandle = Prelude.Nothing,
      body = Prelude.Nothing,
      messageId = Prelude.Nothing,
      messageAttributes = Prelude.Nothing,
      attributes = Prelude.Nothing,
      mD5OfBody = Prelude.Nothing,
      mD5OfMessageAttributes = Prelude.Nothing
    }

-- | An identifier associated with the act of receiving the message. A new
-- receipt handle is returned every time you receive a message. When
-- deleting a message, you provide the last received receipt handle to
-- delete the message.
message_receiptHandle :: Lens.Lens' Message (Prelude.Maybe Prelude.Text)
message_receiptHandle = Lens.lens (\Message' {receiptHandle} -> receiptHandle) (\s@Message' {} a -> s {receiptHandle = a} :: Message)

-- | The message\'s contents (not URL-encoded).
message_body :: Lens.Lens' Message (Prelude.Maybe Prelude.Text)
message_body = Lens.lens (\Message' {body} -> body) (\s@Message' {} a -> s {body = a} :: Message)

-- | A unique identifier for the message. A @MessageId@is considered unique
-- across all accounts for an extended period of time.
message_messageId :: Lens.Lens' Message (Prelude.Maybe Prelude.Text)
message_messageId = Lens.lens (\Message' {messageId} -> messageId) (\s@Message' {} a -> s {messageId = a} :: Message)

-- | Each message attribute consists of a @Name@, @Type@, and @Value@. For
-- more information, see
-- <https://docs.aws.amazon.com/AWSSimpleQueueService/latest/SQSDeveloperGuide/sqs-message-metadata.html#sqs-message-attributes Amazon SQS message attributes>
-- in the /Amazon SQS Developer Guide/.
message_messageAttributes :: Lens.Lens' Message (Prelude.Maybe (Prelude.HashMap Prelude.Text MessageAttributeValue))
message_messageAttributes = Lens.lens (\Message' {messageAttributes} -> messageAttributes) (\s@Message' {} a -> s {messageAttributes = a} :: Message) Prelude.. Lens.mapping Lens.coerced

-- | A map of the attributes requested in @ ReceiveMessage @ to their
-- respective values. Supported attributes:
--
-- -   @ApproximateReceiveCount@
--
-- -   @ApproximateFirstReceiveTimestamp@
--
-- -   @MessageDeduplicationId@
--
-- -   @MessageGroupId@
--
-- -   @SenderId@
--
-- -   @SentTimestamp@
--
-- -   @SequenceNumber@
--
-- @ApproximateFirstReceiveTimestamp@ and @SentTimestamp@ are each returned
-- as an integer representing the
-- <http://en.wikipedia.org/wiki/Unix_time epoch time> in milliseconds.
message_attributes :: Lens.Lens' Message (Prelude.Maybe (Prelude.HashMap MessageAttribute Prelude.Text))
message_attributes = Lens.lens (\Message' {attributes} -> attributes) (\s@Message' {} a -> s {attributes = a} :: Message) Prelude.. Lens.mapping Lens.coerced

-- | An MD5 digest of the non-URL-encoded message body string.
message_mD5OfBody :: Lens.Lens' Message (Prelude.Maybe Prelude.Text)
message_mD5OfBody = Lens.lens (\Message' {mD5OfBody} -> mD5OfBody) (\s@Message' {} a -> s {mD5OfBody = a} :: Message)

-- | An MD5 digest of the non-URL-encoded message attribute string. You can
-- use this attribute to verify that Amazon SQS received the message
-- correctly. Amazon SQS URL-decodes the message before creating the MD5
-- digest. For information about MD5, see
-- <https://www.ietf.org/rfc/rfc1321.txt RFC1321>.
message_mD5OfMessageAttributes :: Lens.Lens' Message (Prelude.Maybe Prelude.Text)
message_mD5OfMessageAttributes = Lens.lens (\Message' {mD5OfMessageAttributes} -> mD5OfMessageAttributes) (\s@Message' {} a -> s {mD5OfMessageAttributes = a} :: Message)

instance Core.FromXML Message where
  parseXML x =
    Message'
      Prelude.<$> (x Core..@? "ReceiptHandle")
      Prelude.<*> (x Core..@? "Body")
      Prelude.<*> (x Core..@? "MessageId")
      Prelude.<*> ( Core.may
                      (Core.parseXMLMap "MessageAttribute" "Name" "Value")
                      x
                  )
      Prelude.<*> ( Core.may
                      (Core.parseXMLMap "Attribute" "Name" "Value")
                      x
                  )
      Prelude.<*> (x Core..@? "MD5OfBody")
      Prelude.<*> (x Core..@? "MD5OfMessageAttributes")

instance Prelude.Hashable Message where
  hashWithSalt _salt Message' {..} =
    _salt `Prelude.hashWithSalt` receiptHandle
      `Prelude.hashWithSalt` body
      `Prelude.hashWithSalt` messageId
      `Prelude.hashWithSalt` messageAttributes
      `Prelude.hashWithSalt` attributes
      `Prelude.hashWithSalt` mD5OfBody
      `Prelude.hashWithSalt` mD5OfMessageAttributes

instance Prelude.NFData Message where
  rnf Message' {..} =
    Prelude.rnf receiptHandle
      `Prelude.seq` Prelude.rnf body
      `Prelude.seq` Prelude.rnf messageId
      `Prelude.seq` Prelude.rnf messageAttributes
      `Prelude.seq` Prelude.rnf attributes
      `Prelude.seq` Prelude.rnf mD5OfBody
      `Prelude.seq` Prelude.rnf mD5OfMessageAttributes
