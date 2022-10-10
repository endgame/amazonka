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
-- Module      : Amazonka.WorkSpacesWeb.Types.UserSettings
-- Copyright   : (c) 2013-2022 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Amazonka.WorkSpacesWeb.Types.UserSettings where

import qualified Amazonka.Core as Core
import qualified Amazonka.Lens as Lens
import qualified Amazonka.Prelude as Prelude
import Amazonka.WorkSpacesWeb.Types.EnabledType

-- | A user settings resource that can be associated with a web portal. Once
-- associated with a web portal, user settings control how users can
-- transfer data between a streaming session and the their local devices.
--
-- /See:/ 'newUserSettings' smart constructor.
data UserSettings = UserSettings'
  { -- | Specifies whether the user can print to the local device.
    printAllowed :: Prelude.Maybe EnabledType,
    -- | A list of web portal ARNs that this user settings is associated with.
    associatedPortalArns :: Prelude.Maybe [Prelude.Text],
    -- | The amount of time that users can be idle (inactive) before they are
    -- disconnected from their streaming session and the disconnect timeout
    -- interval begins.
    idleDisconnectTimeoutInMinutes :: Prelude.Maybe Prelude.Natural,
    -- | The amount of time that a streaming session remains active after users
    -- disconnect.
    disconnectTimeoutInMinutes :: Prelude.Maybe Prelude.Natural,
    -- | Specifies whether the user can copy text from the streaming session to
    -- the local device.
    copyAllowed :: Prelude.Maybe EnabledType,
    -- | Specifies whether the user can download files from the streaming session
    -- to the local device.
    downloadAllowed :: Prelude.Maybe EnabledType,
    -- | Specifies whether the user can paste text from the local device to the
    -- streaming session.
    pasteAllowed :: Prelude.Maybe EnabledType,
    -- | Specifies whether the user can upload files from the local device to the
    -- streaming session.
    uploadAllowed :: Prelude.Maybe EnabledType,
    -- | The ARN of the user settings.
    userSettingsArn :: Prelude.Text
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'UserSettings' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'printAllowed', 'userSettings_printAllowed' - Specifies whether the user can print to the local device.
--
-- 'associatedPortalArns', 'userSettings_associatedPortalArns' - A list of web portal ARNs that this user settings is associated with.
--
-- 'idleDisconnectTimeoutInMinutes', 'userSettings_idleDisconnectTimeoutInMinutes' - The amount of time that users can be idle (inactive) before they are
-- disconnected from their streaming session and the disconnect timeout
-- interval begins.
--
-- 'disconnectTimeoutInMinutes', 'userSettings_disconnectTimeoutInMinutes' - The amount of time that a streaming session remains active after users
-- disconnect.
--
-- 'copyAllowed', 'userSettings_copyAllowed' - Specifies whether the user can copy text from the streaming session to
-- the local device.
--
-- 'downloadAllowed', 'userSettings_downloadAllowed' - Specifies whether the user can download files from the streaming session
-- to the local device.
--
-- 'pasteAllowed', 'userSettings_pasteAllowed' - Specifies whether the user can paste text from the local device to the
-- streaming session.
--
-- 'uploadAllowed', 'userSettings_uploadAllowed' - Specifies whether the user can upload files from the local device to the
-- streaming session.
--
-- 'userSettingsArn', 'userSettings_userSettingsArn' - The ARN of the user settings.
newUserSettings ::
  -- | 'userSettingsArn'
  Prelude.Text ->
  UserSettings
newUserSettings pUserSettingsArn_ =
  UserSettings'
    { printAllowed = Prelude.Nothing,
      associatedPortalArns = Prelude.Nothing,
      idleDisconnectTimeoutInMinutes = Prelude.Nothing,
      disconnectTimeoutInMinutes = Prelude.Nothing,
      copyAllowed = Prelude.Nothing,
      downloadAllowed = Prelude.Nothing,
      pasteAllowed = Prelude.Nothing,
      uploadAllowed = Prelude.Nothing,
      userSettingsArn = pUserSettingsArn_
    }

-- | Specifies whether the user can print to the local device.
userSettings_printAllowed :: Lens.Lens' UserSettings (Prelude.Maybe EnabledType)
userSettings_printAllowed = Lens.lens (\UserSettings' {printAllowed} -> printAllowed) (\s@UserSettings' {} a -> s {printAllowed = a} :: UserSettings)

-- | A list of web portal ARNs that this user settings is associated with.
userSettings_associatedPortalArns :: Lens.Lens' UserSettings (Prelude.Maybe [Prelude.Text])
userSettings_associatedPortalArns = Lens.lens (\UserSettings' {associatedPortalArns} -> associatedPortalArns) (\s@UserSettings' {} a -> s {associatedPortalArns = a} :: UserSettings) Prelude.. Lens.mapping Lens.coerced

-- | The amount of time that users can be idle (inactive) before they are
-- disconnected from their streaming session and the disconnect timeout
-- interval begins.
userSettings_idleDisconnectTimeoutInMinutes :: Lens.Lens' UserSettings (Prelude.Maybe Prelude.Natural)
userSettings_idleDisconnectTimeoutInMinutes = Lens.lens (\UserSettings' {idleDisconnectTimeoutInMinutes} -> idleDisconnectTimeoutInMinutes) (\s@UserSettings' {} a -> s {idleDisconnectTimeoutInMinutes = a} :: UserSettings)

-- | The amount of time that a streaming session remains active after users
-- disconnect.
userSettings_disconnectTimeoutInMinutes :: Lens.Lens' UserSettings (Prelude.Maybe Prelude.Natural)
userSettings_disconnectTimeoutInMinutes = Lens.lens (\UserSettings' {disconnectTimeoutInMinutes} -> disconnectTimeoutInMinutes) (\s@UserSettings' {} a -> s {disconnectTimeoutInMinutes = a} :: UserSettings)

-- | Specifies whether the user can copy text from the streaming session to
-- the local device.
userSettings_copyAllowed :: Lens.Lens' UserSettings (Prelude.Maybe EnabledType)
userSettings_copyAllowed = Lens.lens (\UserSettings' {copyAllowed} -> copyAllowed) (\s@UserSettings' {} a -> s {copyAllowed = a} :: UserSettings)

-- | Specifies whether the user can download files from the streaming session
-- to the local device.
userSettings_downloadAllowed :: Lens.Lens' UserSettings (Prelude.Maybe EnabledType)
userSettings_downloadAllowed = Lens.lens (\UserSettings' {downloadAllowed} -> downloadAllowed) (\s@UserSettings' {} a -> s {downloadAllowed = a} :: UserSettings)

-- | Specifies whether the user can paste text from the local device to the
-- streaming session.
userSettings_pasteAllowed :: Lens.Lens' UserSettings (Prelude.Maybe EnabledType)
userSettings_pasteAllowed = Lens.lens (\UserSettings' {pasteAllowed} -> pasteAllowed) (\s@UserSettings' {} a -> s {pasteAllowed = a} :: UserSettings)

-- | Specifies whether the user can upload files from the local device to the
-- streaming session.
userSettings_uploadAllowed :: Lens.Lens' UserSettings (Prelude.Maybe EnabledType)
userSettings_uploadAllowed = Lens.lens (\UserSettings' {uploadAllowed} -> uploadAllowed) (\s@UserSettings' {} a -> s {uploadAllowed = a} :: UserSettings)

-- | The ARN of the user settings.
userSettings_userSettingsArn :: Lens.Lens' UserSettings Prelude.Text
userSettings_userSettingsArn = Lens.lens (\UserSettings' {userSettingsArn} -> userSettingsArn) (\s@UserSettings' {} a -> s {userSettingsArn = a} :: UserSettings)

instance Core.FromJSON UserSettings where
  parseJSON =
    Core.withObject
      "UserSettings"
      ( \x ->
          UserSettings'
            Prelude.<$> (x Core..:? "printAllowed")
            Prelude.<*> ( x Core..:? "associatedPortalArns"
                            Core..!= Prelude.mempty
                        )
            Prelude.<*> (x Core..:? "idleDisconnectTimeoutInMinutes")
            Prelude.<*> (x Core..:? "disconnectTimeoutInMinutes")
            Prelude.<*> (x Core..:? "copyAllowed")
            Prelude.<*> (x Core..:? "downloadAllowed")
            Prelude.<*> (x Core..:? "pasteAllowed")
            Prelude.<*> (x Core..:? "uploadAllowed")
            Prelude.<*> (x Core..: "userSettingsArn")
      )

instance Prelude.Hashable UserSettings where
  hashWithSalt _salt UserSettings' {..} =
    _salt `Prelude.hashWithSalt` printAllowed
      `Prelude.hashWithSalt` associatedPortalArns
      `Prelude.hashWithSalt` idleDisconnectTimeoutInMinutes
      `Prelude.hashWithSalt` disconnectTimeoutInMinutes
      `Prelude.hashWithSalt` copyAllowed
      `Prelude.hashWithSalt` downloadAllowed
      `Prelude.hashWithSalt` pasteAllowed
      `Prelude.hashWithSalt` uploadAllowed
      `Prelude.hashWithSalt` userSettingsArn

instance Prelude.NFData UserSettings where
  rnf UserSettings' {..} =
    Prelude.rnf printAllowed
      `Prelude.seq` Prelude.rnf associatedPortalArns
      `Prelude.seq` Prelude.rnf idleDisconnectTimeoutInMinutes
      `Prelude.seq` Prelude.rnf disconnectTimeoutInMinutes
      `Prelude.seq` Prelude.rnf copyAllowed
      `Prelude.seq` Prelude.rnf downloadAllowed
      `Prelude.seq` Prelude.rnf pasteAllowed
      `Prelude.seq` Prelude.rnf uploadAllowed
      `Prelude.seq` Prelude.rnf userSettingsArn
