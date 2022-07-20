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
-- Module      : Amazonka.EC2.Types.ClientVpnAuthenticationRequest
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Amazonka.EC2.Types.ClientVpnAuthenticationRequest where

import qualified Amazonka.Core as Core
import Amazonka.EC2.Internal
import Amazonka.EC2.Types.CertificateAuthenticationRequest
import Amazonka.EC2.Types.ClientVpnAuthenticationType
import Amazonka.EC2.Types.DirectoryServiceAuthenticationRequest
import Amazonka.EC2.Types.FederatedAuthenticationRequest
import qualified Amazonka.Lens as Lens
import qualified Amazonka.Prelude as Prelude

-- | Describes the authentication method to be used by a Client VPN endpoint.
-- For more information, see
-- <https://docs.aws.amazon.com/vpn/latest/clientvpn-admin/authentication-authrization.html#client-authentication Authentication>
-- in the /Client VPN Administrator Guide/.
--
-- /See:/ 'newClientVpnAuthenticationRequest' smart constructor.
data ClientVpnAuthenticationRequest = ClientVpnAuthenticationRequest'
  { -- | The type of client authentication to be used.
    type' :: Prelude.Maybe ClientVpnAuthenticationType,
    -- | Information about the IAM SAML identity provider to be used, if
    -- applicable. You must provide this information if __Type__ is
    -- @federated-authentication@.
    federatedAuthentication :: Prelude.Maybe FederatedAuthenticationRequest,
    -- | Information about the authentication certificates to be used, if
    -- applicable. You must provide this information if __Type__ is
    -- @certificate-authentication@.
    mutualAuthentication :: Prelude.Maybe CertificateAuthenticationRequest,
    -- | Information about the Active Directory to be used, if applicable. You
    -- must provide this information if __Type__ is
    -- @directory-service-authentication@.
    activeDirectory :: Prelude.Maybe DirectoryServiceAuthenticationRequest
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'ClientVpnAuthenticationRequest' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'type'', 'clientVpnAuthenticationRequest_type' - The type of client authentication to be used.
--
-- 'federatedAuthentication', 'clientVpnAuthenticationRequest_federatedAuthentication' - Information about the IAM SAML identity provider to be used, if
-- applicable. You must provide this information if __Type__ is
-- @federated-authentication@.
--
-- 'mutualAuthentication', 'clientVpnAuthenticationRequest_mutualAuthentication' - Information about the authentication certificates to be used, if
-- applicable. You must provide this information if __Type__ is
-- @certificate-authentication@.
--
-- 'activeDirectory', 'clientVpnAuthenticationRequest_activeDirectory' - Information about the Active Directory to be used, if applicable. You
-- must provide this information if __Type__ is
-- @directory-service-authentication@.
newClientVpnAuthenticationRequest ::
  ClientVpnAuthenticationRequest
newClientVpnAuthenticationRequest =
  ClientVpnAuthenticationRequest'
    { type' =
        Prelude.Nothing,
      federatedAuthentication = Prelude.Nothing,
      mutualAuthentication = Prelude.Nothing,
      activeDirectory = Prelude.Nothing
    }

-- | The type of client authentication to be used.
clientVpnAuthenticationRequest_type :: Lens.Lens' ClientVpnAuthenticationRequest (Prelude.Maybe ClientVpnAuthenticationType)
clientVpnAuthenticationRequest_type = Lens.lens (\ClientVpnAuthenticationRequest' {type'} -> type') (\s@ClientVpnAuthenticationRequest' {} a -> s {type' = a} :: ClientVpnAuthenticationRequest)

-- | Information about the IAM SAML identity provider to be used, if
-- applicable. You must provide this information if __Type__ is
-- @federated-authentication@.
clientVpnAuthenticationRequest_federatedAuthentication :: Lens.Lens' ClientVpnAuthenticationRequest (Prelude.Maybe FederatedAuthenticationRequest)
clientVpnAuthenticationRequest_federatedAuthentication = Lens.lens (\ClientVpnAuthenticationRequest' {federatedAuthentication} -> federatedAuthentication) (\s@ClientVpnAuthenticationRequest' {} a -> s {federatedAuthentication = a} :: ClientVpnAuthenticationRequest)

-- | Information about the authentication certificates to be used, if
-- applicable. You must provide this information if __Type__ is
-- @certificate-authentication@.
clientVpnAuthenticationRequest_mutualAuthentication :: Lens.Lens' ClientVpnAuthenticationRequest (Prelude.Maybe CertificateAuthenticationRequest)
clientVpnAuthenticationRequest_mutualAuthentication = Lens.lens (\ClientVpnAuthenticationRequest' {mutualAuthentication} -> mutualAuthentication) (\s@ClientVpnAuthenticationRequest' {} a -> s {mutualAuthentication = a} :: ClientVpnAuthenticationRequest)

-- | Information about the Active Directory to be used, if applicable. You
-- must provide this information if __Type__ is
-- @directory-service-authentication@.
clientVpnAuthenticationRequest_activeDirectory :: Lens.Lens' ClientVpnAuthenticationRequest (Prelude.Maybe DirectoryServiceAuthenticationRequest)
clientVpnAuthenticationRequest_activeDirectory = Lens.lens (\ClientVpnAuthenticationRequest' {activeDirectory} -> activeDirectory) (\s@ClientVpnAuthenticationRequest' {} a -> s {activeDirectory = a} :: ClientVpnAuthenticationRequest)

instance
  Prelude.Hashable
    ClientVpnAuthenticationRequest
  where
  hashWithSalt
    _salt
    ClientVpnAuthenticationRequest' {..} =
      _salt `Prelude.hashWithSalt` type'
        `Prelude.hashWithSalt` federatedAuthentication
        `Prelude.hashWithSalt` mutualAuthentication
        `Prelude.hashWithSalt` activeDirectory

instance
  Prelude.NFData
    ClientVpnAuthenticationRequest
  where
  rnf ClientVpnAuthenticationRequest' {..} =
    Prelude.rnf type'
      `Prelude.seq` Prelude.rnf federatedAuthentication
      `Prelude.seq` Prelude.rnf mutualAuthentication
      `Prelude.seq` Prelude.rnf activeDirectory

instance Core.ToQuery ClientVpnAuthenticationRequest where
  toQuery ClientVpnAuthenticationRequest' {..} =
    Prelude.mconcat
      [ "Type" Core.=: type',
        "FederatedAuthentication"
          Core.=: federatedAuthentication,
        "MutualAuthentication" Core.=: mutualAuthentication,
        "ActiveDirectory" Core.=: activeDirectory
      ]
