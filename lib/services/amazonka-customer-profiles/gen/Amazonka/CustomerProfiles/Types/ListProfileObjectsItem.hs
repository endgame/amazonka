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
-- Module      : Amazonka.CustomerProfiles.Types.ListProfileObjectsItem
-- Copyright   : (c) 2013-2023 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Amazonka.CustomerProfiles.Types.ListProfileObjectsItem where

import qualified Amazonka.Core as Core
import qualified Amazonka.Core.Lens.Internal as Lens
import qualified Amazonka.Data as Data
import qualified Amazonka.Prelude as Prelude

-- | A ProfileObject in a list of ProfileObjects.
--
-- /See:/ 'newListProfileObjectsItem' smart constructor.
data ListProfileObjectsItem = ListProfileObjectsItem'
  { -- | A JSON representation of a ProfileObject that belongs to a profile.
    object' :: Prelude.Maybe Prelude.Text,
    -- | Specifies the kind of object being added to a profile, such as
    -- \"Salesforce-Account.\"
    objectTypeName :: Prelude.Maybe Prelude.Text,
    -- | The unique identifier of the ProfileObject generated by the service.
    profileObjectUniqueKey :: Prelude.Maybe Prelude.Text
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'ListProfileObjectsItem' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'object'', 'listProfileObjectsItem_object' - A JSON representation of a ProfileObject that belongs to a profile.
--
-- 'objectTypeName', 'listProfileObjectsItem_objectTypeName' - Specifies the kind of object being added to a profile, such as
-- \"Salesforce-Account.\"
--
-- 'profileObjectUniqueKey', 'listProfileObjectsItem_profileObjectUniqueKey' - The unique identifier of the ProfileObject generated by the service.
newListProfileObjectsItem ::
  ListProfileObjectsItem
newListProfileObjectsItem =
  ListProfileObjectsItem'
    { object' = Prelude.Nothing,
      objectTypeName = Prelude.Nothing,
      profileObjectUniqueKey = Prelude.Nothing
    }

-- | A JSON representation of a ProfileObject that belongs to a profile.
listProfileObjectsItem_object :: Lens.Lens' ListProfileObjectsItem (Prelude.Maybe Prelude.Text)
listProfileObjectsItem_object = Lens.lens (\ListProfileObjectsItem' {object'} -> object') (\s@ListProfileObjectsItem' {} a -> s {object' = a} :: ListProfileObjectsItem)

-- | Specifies the kind of object being added to a profile, such as
-- \"Salesforce-Account.\"
listProfileObjectsItem_objectTypeName :: Lens.Lens' ListProfileObjectsItem (Prelude.Maybe Prelude.Text)
listProfileObjectsItem_objectTypeName = Lens.lens (\ListProfileObjectsItem' {objectTypeName} -> objectTypeName) (\s@ListProfileObjectsItem' {} a -> s {objectTypeName = a} :: ListProfileObjectsItem)

-- | The unique identifier of the ProfileObject generated by the service.
listProfileObjectsItem_profileObjectUniqueKey :: Lens.Lens' ListProfileObjectsItem (Prelude.Maybe Prelude.Text)
listProfileObjectsItem_profileObjectUniqueKey = Lens.lens (\ListProfileObjectsItem' {profileObjectUniqueKey} -> profileObjectUniqueKey) (\s@ListProfileObjectsItem' {} a -> s {profileObjectUniqueKey = a} :: ListProfileObjectsItem)

instance Data.FromJSON ListProfileObjectsItem where
  parseJSON =
    Data.withObject
      "ListProfileObjectsItem"
      ( \x ->
          ListProfileObjectsItem'
            Prelude.<$> (x Data..:? "Object")
            Prelude.<*> (x Data..:? "ObjectTypeName")
            Prelude.<*> (x Data..:? "ProfileObjectUniqueKey")
      )

instance Prelude.Hashable ListProfileObjectsItem where
  hashWithSalt _salt ListProfileObjectsItem' {..} =
    _salt
      `Prelude.hashWithSalt` object'
      `Prelude.hashWithSalt` objectTypeName
      `Prelude.hashWithSalt` profileObjectUniqueKey

instance Prelude.NFData ListProfileObjectsItem where
  rnf ListProfileObjectsItem' {..} =
    Prelude.rnf object' `Prelude.seq`
      Prelude.rnf objectTypeName `Prelude.seq`
        Prelude.rnf profileObjectUniqueKey
