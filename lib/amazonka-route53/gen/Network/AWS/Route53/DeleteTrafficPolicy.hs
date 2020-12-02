{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

-- Derived from AWS service descriptions, licensed under Apache 2.0.

-- |
-- Module      : Network.AWS.Route53.DeleteTrafficPolicy
-- Copyright   : (c) 2013-2020 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
--
-- Deletes a traffic policy.
--
--
-- When you delete a traffic policy, Route 53 sets a flag on the policy to indicate that it has been deleted. However, Route 53 never fully deletes the traffic policy. Note the following:
--
--     * Deleted traffic policies aren't listed if you run <https://docs.aws.amazon.com/Route53/latest/APIReference/API_ListTrafficPolicies.html ListTrafficPolicies> .
--
--     * There's no way to get a list of deleted policies.
--
--     * If you retain the ID of the policy, you can get information about the policy, including the traffic policy document, by running <https://docs.aws.amazon.com/Route53/latest/APIReference/API_GetTrafficPolicy.html GetTrafficPolicy> .
module Network.AWS.Route53.DeleteTrafficPolicy
  ( -- * Creating a Request
    deleteTrafficPolicy,
    DeleteTrafficPolicy,

    -- * Request Lenses
    dtpId,
    dtpVersion,

    -- * Destructuring the Response
    deleteTrafficPolicyResponse,
    DeleteTrafficPolicyResponse,

    -- * Response Lenses
    dtprsResponseStatus,
  )
where

import Network.AWS.Lens
import Network.AWS.Prelude
import Network.AWS.Request
import Network.AWS.Response
import Network.AWS.Route53.Types

-- | A request to delete a specified traffic policy version.
--
--
--
-- /See:/ 'deleteTrafficPolicy' smart constructor.
data DeleteTrafficPolicy = DeleteTrafficPolicy'
  { _dtpId :: !Text,
    _dtpVersion :: !Nat
  }
  deriving (Eq, Read, Show, Data, Typeable, Generic)

-- | Creates a value of 'DeleteTrafficPolicy' with the minimum fields required to make a request.
--
-- Use one of the following lenses to modify other fields as desired:
--
-- * 'dtpId' - The ID of the traffic policy that you want to delete.
--
-- * 'dtpVersion' - The version number of the traffic policy that you want to delete.
deleteTrafficPolicy ::
  -- | 'dtpId'
  Text ->
  -- | 'dtpVersion'
  Natural ->
  DeleteTrafficPolicy
deleteTrafficPolicy pId_ pVersion_ =
  DeleteTrafficPolicy'
    { _dtpId = pId_,
      _dtpVersion = _Nat # pVersion_
    }

-- | The ID of the traffic policy that you want to delete.
dtpId :: Lens' DeleteTrafficPolicy Text
dtpId = lens _dtpId (\s a -> s {_dtpId = a})

-- | The version number of the traffic policy that you want to delete.
dtpVersion :: Lens' DeleteTrafficPolicy Natural
dtpVersion = lens _dtpVersion (\s a -> s {_dtpVersion = a}) . _Nat

instance AWSRequest DeleteTrafficPolicy where
  type Rs DeleteTrafficPolicy = DeleteTrafficPolicyResponse
  request = delete route53
  response =
    receiveEmpty
      (\s h x -> DeleteTrafficPolicyResponse' <$> (pure (fromEnum s)))

instance Hashable DeleteTrafficPolicy

instance NFData DeleteTrafficPolicy

instance ToHeaders DeleteTrafficPolicy where
  toHeaders = const mempty

instance ToPath DeleteTrafficPolicy where
  toPath DeleteTrafficPolicy' {..} =
    mconcat
      ["/2013-04-01/trafficpolicy/", toBS _dtpId, "/", toBS _dtpVersion]

instance ToQuery DeleteTrafficPolicy where
  toQuery = const mempty

-- | An empty element.
--
--
--
-- /See:/ 'deleteTrafficPolicyResponse' smart constructor.
newtype DeleteTrafficPolicyResponse = DeleteTrafficPolicyResponse'
  { _dtprsResponseStatus ::
      Int
  }
  deriving (Eq, Read, Show, Data, Typeable, Generic)

-- | Creates a value of 'DeleteTrafficPolicyResponse' with the minimum fields required to make a request.
--
-- Use one of the following lenses to modify other fields as desired:
--
-- * 'dtprsResponseStatus' - -- | The response status code.
deleteTrafficPolicyResponse ::
  -- | 'dtprsResponseStatus'
  Int ->
  DeleteTrafficPolicyResponse
deleteTrafficPolicyResponse pResponseStatus_ =
  DeleteTrafficPolicyResponse'
    { _dtprsResponseStatus =
        pResponseStatus_
    }

-- | -- | The response status code.
dtprsResponseStatus :: Lens' DeleteTrafficPolicyResponse Int
dtprsResponseStatus = lens _dtprsResponseStatus (\s a -> s {_dtprsResponseStatus = a})

instance NFData DeleteTrafficPolicyResponse