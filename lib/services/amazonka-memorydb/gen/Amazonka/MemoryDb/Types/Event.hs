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
-- Module      : Amazonka.MemoryDb.Types.Event
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Amazonka.MemoryDb.Types.Event where

import qualified Amazonka.Core as Core
import qualified Amazonka.Lens as Lens
import Amazonka.MemoryDb.Types.SourceType
import qualified Amazonka.Prelude as Prelude

-- | Represents a single occurrence of something interesting within the
-- system. Some examples of events are creating a cluster or adding or
-- removing a node.
--
-- /See:/ 'newEvent' smart constructor.
data Event = Event'
  { -- | The text of the event.
    message :: Prelude.Maybe Prelude.Text,
    -- | The name for the source of the event. For example, if the event occurred
    -- at the cluster level, the identifier would be the name of the cluster.
    sourceName :: Prelude.Maybe Prelude.Text,
    -- | The date and time when the event occurred.
    date :: Prelude.Maybe Core.POSIX,
    -- | Specifies the origin of this event - a cluster, a parameter group, a
    -- security group, etc.
    sourceType :: Prelude.Maybe SourceType
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'Event' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'message', 'event_message' - The text of the event.
--
-- 'sourceName', 'event_sourceName' - The name for the source of the event. For example, if the event occurred
-- at the cluster level, the identifier would be the name of the cluster.
--
-- 'date', 'event_date' - The date and time when the event occurred.
--
-- 'sourceType', 'event_sourceType' - Specifies the origin of this event - a cluster, a parameter group, a
-- security group, etc.
newEvent ::
  Event
newEvent =
  Event'
    { message = Prelude.Nothing,
      sourceName = Prelude.Nothing,
      date = Prelude.Nothing,
      sourceType = Prelude.Nothing
    }

-- | The text of the event.
event_message :: Lens.Lens' Event (Prelude.Maybe Prelude.Text)
event_message = Lens.lens (\Event' {message} -> message) (\s@Event' {} a -> s {message = a} :: Event)

-- | The name for the source of the event. For example, if the event occurred
-- at the cluster level, the identifier would be the name of the cluster.
event_sourceName :: Lens.Lens' Event (Prelude.Maybe Prelude.Text)
event_sourceName = Lens.lens (\Event' {sourceName} -> sourceName) (\s@Event' {} a -> s {sourceName = a} :: Event)

-- | The date and time when the event occurred.
event_date :: Lens.Lens' Event (Prelude.Maybe Prelude.UTCTime)
event_date = Lens.lens (\Event' {date} -> date) (\s@Event' {} a -> s {date = a} :: Event) Prelude.. Lens.mapping Core._Time

-- | Specifies the origin of this event - a cluster, a parameter group, a
-- security group, etc.
event_sourceType :: Lens.Lens' Event (Prelude.Maybe SourceType)
event_sourceType = Lens.lens (\Event' {sourceType} -> sourceType) (\s@Event' {} a -> s {sourceType = a} :: Event)

instance Core.FromJSON Event where
  parseJSON =
    Core.withObject
      "Event"
      ( \x ->
          Event'
            Prelude.<$> (x Core..:? "Message")
            Prelude.<*> (x Core..:? "SourceName")
            Prelude.<*> (x Core..:? "Date")
            Prelude.<*> (x Core..:? "SourceType")
      )

instance Prelude.Hashable Event where
  hashWithSalt _salt Event' {..} =
    _salt `Prelude.hashWithSalt` message
      `Prelude.hashWithSalt` sourceName
      `Prelude.hashWithSalt` date
      `Prelude.hashWithSalt` sourceType

instance Prelude.NFData Event where
  rnf Event' {..} =
    Prelude.rnf message
      `Prelude.seq` Prelude.rnf sourceName
      `Prelude.seq` Prelude.rnf date
      `Prelude.seq` Prelude.rnf sourceType
