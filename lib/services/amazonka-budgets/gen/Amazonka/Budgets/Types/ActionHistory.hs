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
-- Module      : Amazonka.Budgets.Types.ActionHistory
-- Copyright   : (c) 2013-2023 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Amazonka.Budgets.Types.ActionHistory where

import Amazonka.Budgets.Types.ActionHistoryDetails
import Amazonka.Budgets.Types.ActionStatus
import Amazonka.Budgets.Types.EventType
import qualified Amazonka.Core as Core
import qualified Amazonka.Core.Lens.Internal as Lens
import qualified Amazonka.Data as Data
import qualified Amazonka.Prelude as Prelude

-- | The historical records for a budget action.
--
-- /See:/ 'newActionHistory' smart constructor.
data ActionHistory = ActionHistory'
  { timestamp :: Data.POSIX,
    -- | The status of action at the time of the event.
    status :: ActionStatus,
    -- | This distinguishes between whether the events are triggered by the user
    -- or are generated by the system.
    eventType :: EventType,
    -- | The description of the details for the event.
    actionHistoryDetails :: ActionHistoryDetails
  }
  deriving (Prelude.Eq, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'ActionHistory' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'timestamp', 'actionHistory_timestamp' - Undocumented member.
--
-- 'status', 'actionHistory_status' - The status of action at the time of the event.
--
-- 'eventType', 'actionHistory_eventType' - This distinguishes between whether the events are triggered by the user
-- or are generated by the system.
--
-- 'actionHistoryDetails', 'actionHistory_actionHistoryDetails' - The description of the details for the event.
newActionHistory ::
  -- | 'timestamp'
  Prelude.UTCTime ->
  -- | 'status'
  ActionStatus ->
  -- | 'eventType'
  EventType ->
  -- | 'actionHistoryDetails'
  ActionHistoryDetails ->
  ActionHistory
newActionHistory
  pTimestamp_
  pStatus_
  pEventType_
  pActionHistoryDetails_ =
    ActionHistory'
      { timestamp =
          Data._Time Lens.# pTimestamp_,
        status = pStatus_,
        eventType = pEventType_,
        actionHistoryDetails = pActionHistoryDetails_
      }

-- | Undocumented member.
actionHistory_timestamp :: Lens.Lens' ActionHistory Prelude.UTCTime
actionHistory_timestamp = Lens.lens (\ActionHistory' {timestamp} -> timestamp) (\s@ActionHistory' {} a -> s {timestamp = a} :: ActionHistory) Prelude.. Data._Time

-- | The status of action at the time of the event.
actionHistory_status :: Lens.Lens' ActionHistory ActionStatus
actionHistory_status = Lens.lens (\ActionHistory' {status} -> status) (\s@ActionHistory' {} a -> s {status = a} :: ActionHistory)

-- | This distinguishes between whether the events are triggered by the user
-- or are generated by the system.
actionHistory_eventType :: Lens.Lens' ActionHistory EventType
actionHistory_eventType = Lens.lens (\ActionHistory' {eventType} -> eventType) (\s@ActionHistory' {} a -> s {eventType = a} :: ActionHistory)

-- | The description of the details for the event.
actionHistory_actionHistoryDetails :: Lens.Lens' ActionHistory ActionHistoryDetails
actionHistory_actionHistoryDetails = Lens.lens (\ActionHistory' {actionHistoryDetails} -> actionHistoryDetails) (\s@ActionHistory' {} a -> s {actionHistoryDetails = a} :: ActionHistory)

instance Data.FromJSON ActionHistory where
  parseJSON =
    Data.withObject
      "ActionHistory"
      ( \x ->
          ActionHistory'
            Prelude.<$> (x Data..: "Timestamp")
            Prelude.<*> (x Data..: "Status")
            Prelude.<*> (x Data..: "EventType")
            Prelude.<*> (x Data..: "ActionHistoryDetails")
      )

instance Prelude.Hashable ActionHistory where
  hashWithSalt _salt ActionHistory' {..} =
    _salt
      `Prelude.hashWithSalt` timestamp
      `Prelude.hashWithSalt` status
      `Prelude.hashWithSalt` eventType
      `Prelude.hashWithSalt` actionHistoryDetails

instance Prelude.NFData ActionHistory where
  rnf ActionHistory' {..} =
    Prelude.rnf timestamp `Prelude.seq`
      Prelude.rnf status `Prelude.seq`
        Prelude.rnf eventType `Prelude.seq`
          Prelude.rnf actionHistoryDetails
