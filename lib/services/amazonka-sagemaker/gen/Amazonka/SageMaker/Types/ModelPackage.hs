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
-- Module      : Amazonka.SageMaker.Types.ModelPackage
-- Copyright   : (c) 2013-2021 Brendan Hay
-- License     : Mozilla Public License, v. 2.0.
-- Maintainer  : Brendan Hay <brendan.g.hay+amazonka@gmail.com>
-- Stability   : auto-generated
-- Portability : non-portable (GHC extensions)
module Amazonka.SageMaker.Types.ModelPackage where

import qualified Amazonka.Core as Core
import qualified Amazonka.Lens as Lens
import qualified Amazonka.Prelude as Prelude
import Amazonka.SageMaker.Types.InferenceSpecification
import Amazonka.SageMaker.Types.MetadataProperties
import Amazonka.SageMaker.Types.ModelApprovalStatus
import Amazonka.SageMaker.Types.ModelMetrics
import Amazonka.SageMaker.Types.ModelPackageStatus
import Amazonka.SageMaker.Types.ModelPackageStatusDetails
import Amazonka.SageMaker.Types.ModelPackageValidationSpecification
import Amazonka.SageMaker.Types.SourceAlgorithmSpecification
import Amazonka.SageMaker.Types.Tag
import Amazonka.SageMaker.Types.UserContext

-- | A versioned model that can be deployed for SageMaker inference.
--
-- /See:/ 'newModelPackage' smart constructor.
data ModelPackage = ModelPackage'
  { -- | A list of the tags associated with the model package. For more
    -- information, see
    -- <https://docs.aws.amazon.com/general/latest/gr/aws_tagging.html Tagging Amazon Web Services resources>
    -- in the /Amazon Web Services General Reference Guide/.
    tags :: Prelude.Maybe [Tag],
    -- | The version number of a versioned model.
    modelPackageVersion :: Prelude.Maybe Prelude.Natural,
    -- | The model group to which the model belongs.
    modelPackageGroupName :: Prelude.Maybe Prelude.Text,
    sourceAlgorithmSpecification :: Prelude.Maybe SourceAlgorithmSpecification,
    validationSpecification :: Prelude.Maybe ModelPackageValidationSpecification,
    -- | Whether the model package is to be certified to be listed on Amazon Web
    -- Services Marketplace. For information about listing model packages on
    -- Amazon Web Services Marketplace, see
    -- <https://docs.aws.amazon.com/sagemaker/latest/dg/sagemaker-mkt-list.html List Your Algorithm or Model Package on Amazon Web Services Marketplace>.
    certifyForMarketplace :: Prelude.Maybe Prelude.Bool,
    inferenceSpecification :: Prelude.Maybe InferenceSpecification,
    -- | The approval status of the model. This can be one of the following
    -- values.
    --
    -- -   @APPROVED@ - The model is approved
    --
    -- -   @REJECTED@ - The model is rejected.
    --
    -- -   @PENDING_MANUAL_APPROVAL@ - The model is waiting for manual
    --     approval.
    modelApprovalStatus :: Prelude.Maybe ModelApprovalStatus,
    metadataProperties :: Prelude.Maybe MetadataProperties,
    -- | The description of the model package.
    modelPackageDescription :: Prelude.Maybe Prelude.Text,
    -- | A description provided when the model approval is set.
    approvalDescription :: Prelude.Maybe Prelude.Text,
    -- | The Amazon Resource Name (ARN) of the model package.
    modelPackageArn :: Prelude.Maybe Prelude.Text,
    -- | The last time the model package was modified.
    lastModifiedTime :: Prelude.Maybe Core.POSIX,
    -- | The status of the model package. This can be one of the following
    -- values.
    --
    -- -   @PENDING@ - The model package is pending being created.
    --
    -- -   @IN_PROGRESS@ - The model package is in the process of being
    --     created.
    --
    -- -   @COMPLETED@ - The model package was successfully created.
    --
    -- -   @FAILED@ - The model package failed.
    --
    -- -   @DELETING@ - The model package is in the process of being deleted.
    modelPackageStatus :: Prelude.Maybe ModelPackageStatus,
    -- | Metrics for the model.
    modelMetrics :: Prelude.Maybe ModelMetrics,
    modelPackageStatusDetails :: Prelude.Maybe ModelPackageStatusDetails,
    -- | The time that the model package was created.
    creationTime :: Prelude.Maybe Core.POSIX,
    lastModifiedBy :: Prelude.Maybe UserContext,
    createdBy :: Prelude.Maybe UserContext,
    -- | The name of the model.
    modelPackageName :: Prelude.Maybe Prelude.Text
  }
  deriving (Prelude.Eq, Prelude.Read, Prelude.Show, Prelude.Generic)

-- |
-- Create a value of 'ModelPackage' with all optional fields omitted.
--
-- Use <https://hackage.haskell.org/package/generic-lens generic-lens> or <https://hackage.haskell.org/package/optics optics> to modify other optional fields.
--
-- The following record fields are available, with the corresponding lenses provided
-- for backwards compatibility:
--
-- 'tags', 'modelPackage_tags' - A list of the tags associated with the model package. For more
-- information, see
-- <https://docs.aws.amazon.com/general/latest/gr/aws_tagging.html Tagging Amazon Web Services resources>
-- in the /Amazon Web Services General Reference Guide/.
--
-- 'modelPackageVersion', 'modelPackage_modelPackageVersion' - The version number of a versioned model.
--
-- 'modelPackageGroupName', 'modelPackage_modelPackageGroupName' - The model group to which the model belongs.
--
-- 'sourceAlgorithmSpecification', 'modelPackage_sourceAlgorithmSpecification' - Undocumented member.
--
-- 'validationSpecification', 'modelPackage_validationSpecification' - Undocumented member.
--
-- 'certifyForMarketplace', 'modelPackage_certifyForMarketplace' - Whether the model package is to be certified to be listed on Amazon Web
-- Services Marketplace. For information about listing model packages on
-- Amazon Web Services Marketplace, see
-- <https://docs.aws.amazon.com/sagemaker/latest/dg/sagemaker-mkt-list.html List Your Algorithm or Model Package on Amazon Web Services Marketplace>.
--
-- 'inferenceSpecification', 'modelPackage_inferenceSpecification' - Undocumented member.
--
-- 'modelApprovalStatus', 'modelPackage_modelApprovalStatus' - The approval status of the model. This can be one of the following
-- values.
--
-- -   @APPROVED@ - The model is approved
--
-- -   @REJECTED@ - The model is rejected.
--
-- -   @PENDING_MANUAL_APPROVAL@ - The model is waiting for manual
--     approval.
--
-- 'metadataProperties', 'modelPackage_metadataProperties' - Undocumented member.
--
-- 'modelPackageDescription', 'modelPackage_modelPackageDescription' - The description of the model package.
--
-- 'approvalDescription', 'modelPackage_approvalDescription' - A description provided when the model approval is set.
--
-- 'modelPackageArn', 'modelPackage_modelPackageArn' - The Amazon Resource Name (ARN) of the model package.
--
-- 'lastModifiedTime', 'modelPackage_lastModifiedTime' - The last time the model package was modified.
--
-- 'modelPackageStatus', 'modelPackage_modelPackageStatus' - The status of the model package. This can be one of the following
-- values.
--
-- -   @PENDING@ - The model package is pending being created.
--
-- -   @IN_PROGRESS@ - The model package is in the process of being
--     created.
--
-- -   @COMPLETED@ - The model package was successfully created.
--
-- -   @FAILED@ - The model package failed.
--
-- -   @DELETING@ - The model package is in the process of being deleted.
--
-- 'modelMetrics', 'modelPackage_modelMetrics' - Metrics for the model.
--
-- 'modelPackageStatusDetails', 'modelPackage_modelPackageStatusDetails' - Undocumented member.
--
-- 'creationTime', 'modelPackage_creationTime' - The time that the model package was created.
--
-- 'lastModifiedBy', 'modelPackage_lastModifiedBy' - Undocumented member.
--
-- 'createdBy', 'modelPackage_createdBy' - Undocumented member.
--
-- 'modelPackageName', 'modelPackage_modelPackageName' - The name of the model.
newModelPackage ::
  ModelPackage
newModelPackage =
  ModelPackage'
    { tags = Prelude.Nothing,
      modelPackageVersion = Prelude.Nothing,
      modelPackageGroupName = Prelude.Nothing,
      sourceAlgorithmSpecification = Prelude.Nothing,
      validationSpecification = Prelude.Nothing,
      certifyForMarketplace = Prelude.Nothing,
      inferenceSpecification = Prelude.Nothing,
      modelApprovalStatus = Prelude.Nothing,
      metadataProperties = Prelude.Nothing,
      modelPackageDescription = Prelude.Nothing,
      approvalDescription = Prelude.Nothing,
      modelPackageArn = Prelude.Nothing,
      lastModifiedTime = Prelude.Nothing,
      modelPackageStatus = Prelude.Nothing,
      modelMetrics = Prelude.Nothing,
      modelPackageStatusDetails = Prelude.Nothing,
      creationTime = Prelude.Nothing,
      lastModifiedBy = Prelude.Nothing,
      createdBy = Prelude.Nothing,
      modelPackageName = Prelude.Nothing
    }

-- | A list of the tags associated with the model package. For more
-- information, see
-- <https://docs.aws.amazon.com/general/latest/gr/aws_tagging.html Tagging Amazon Web Services resources>
-- in the /Amazon Web Services General Reference Guide/.
modelPackage_tags :: Lens.Lens' ModelPackage (Prelude.Maybe [Tag])
modelPackage_tags = Lens.lens (\ModelPackage' {tags} -> tags) (\s@ModelPackage' {} a -> s {tags = a} :: ModelPackage) Prelude.. Lens.mapping Lens.coerced

-- | The version number of a versioned model.
modelPackage_modelPackageVersion :: Lens.Lens' ModelPackage (Prelude.Maybe Prelude.Natural)
modelPackage_modelPackageVersion = Lens.lens (\ModelPackage' {modelPackageVersion} -> modelPackageVersion) (\s@ModelPackage' {} a -> s {modelPackageVersion = a} :: ModelPackage)

-- | The model group to which the model belongs.
modelPackage_modelPackageGroupName :: Lens.Lens' ModelPackage (Prelude.Maybe Prelude.Text)
modelPackage_modelPackageGroupName = Lens.lens (\ModelPackage' {modelPackageGroupName} -> modelPackageGroupName) (\s@ModelPackage' {} a -> s {modelPackageGroupName = a} :: ModelPackage)

-- | Undocumented member.
modelPackage_sourceAlgorithmSpecification :: Lens.Lens' ModelPackage (Prelude.Maybe SourceAlgorithmSpecification)
modelPackage_sourceAlgorithmSpecification = Lens.lens (\ModelPackage' {sourceAlgorithmSpecification} -> sourceAlgorithmSpecification) (\s@ModelPackage' {} a -> s {sourceAlgorithmSpecification = a} :: ModelPackage)

-- | Undocumented member.
modelPackage_validationSpecification :: Lens.Lens' ModelPackage (Prelude.Maybe ModelPackageValidationSpecification)
modelPackage_validationSpecification = Lens.lens (\ModelPackage' {validationSpecification} -> validationSpecification) (\s@ModelPackage' {} a -> s {validationSpecification = a} :: ModelPackage)

-- | Whether the model package is to be certified to be listed on Amazon Web
-- Services Marketplace. For information about listing model packages on
-- Amazon Web Services Marketplace, see
-- <https://docs.aws.amazon.com/sagemaker/latest/dg/sagemaker-mkt-list.html List Your Algorithm or Model Package on Amazon Web Services Marketplace>.
modelPackage_certifyForMarketplace :: Lens.Lens' ModelPackage (Prelude.Maybe Prelude.Bool)
modelPackage_certifyForMarketplace = Lens.lens (\ModelPackage' {certifyForMarketplace} -> certifyForMarketplace) (\s@ModelPackage' {} a -> s {certifyForMarketplace = a} :: ModelPackage)

-- | Undocumented member.
modelPackage_inferenceSpecification :: Lens.Lens' ModelPackage (Prelude.Maybe InferenceSpecification)
modelPackage_inferenceSpecification = Lens.lens (\ModelPackage' {inferenceSpecification} -> inferenceSpecification) (\s@ModelPackage' {} a -> s {inferenceSpecification = a} :: ModelPackage)

-- | The approval status of the model. This can be one of the following
-- values.
--
-- -   @APPROVED@ - The model is approved
--
-- -   @REJECTED@ - The model is rejected.
--
-- -   @PENDING_MANUAL_APPROVAL@ - The model is waiting for manual
--     approval.
modelPackage_modelApprovalStatus :: Lens.Lens' ModelPackage (Prelude.Maybe ModelApprovalStatus)
modelPackage_modelApprovalStatus = Lens.lens (\ModelPackage' {modelApprovalStatus} -> modelApprovalStatus) (\s@ModelPackage' {} a -> s {modelApprovalStatus = a} :: ModelPackage)

-- | Undocumented member.
modelPackage_metadataProperties :: Lens.Lens' ModelPackage (Prelude.Maybe MetadataProperties)
modelPackage_metadataProperties = Lens.lens (\ModelPackage' {metadataProperties} -> metadataProperties) (\s@ModelPackage' {} a -> s {metadataProperties = a} :: ModelPackage)

-- | The description of the model package.
modelPackage_modelPackageDescription :: Lens.Lens' ModelPackage (Prelude.Maybe Prelude.Text)
modelPackage_modelPackageDescription = Lens.lens (\ModelPackage' {modelPackageDescription} -> modelPackageDescription) (\s@ModelPackage' {} a -> s {modelPackageDescription = a} :: ModelPackage)

-- | A description provided when the model approval is set.
modelPackage_approvalDescription :: Lens.Lens' ModelPackage (Prelude.Maybe Prelude.Text)
modelPackage_approvalDescription = Lens.lens (\ModelPackage' {approvalDescription} -> approvalDescription) (\s@ModelPackage' {} a -> s {approvalDescription = a} :: ModelPackage)

-- | The Amazon Resource Name (ARN) of the model package.
modelPackage_modelPackageArn :: Lens.Lens' ModelPackage (Prelude.Maybe Prelude.Text)
modelPackage_modelPackageArn = Lens.lens (\ModelPackage' {modelPackageArn} -> modelPackageArn) (\s@ModelPackage' {} a -> s {modelPackageArn = a} :: ModelPackage)

-- | The last time the model package was modified.
modelPackage_lastModifiedTime :: Lens.Lens' ModelPackage (Prelude.Maybe Prelude.UTCTime)
modelPackage_lastModifiedTime = Lens.lens (\ModelPackage' {lastModifiedTime} -> lastModifiedTime) (\s@ModelPackage' {} a -> s {lastModifiedTime = a} :: ModelPackage) Prelude.. Lens.mapping Core._Time

-- | The status of the model package. This can be one of the following
-- values.
--
-- -   @PENDING@ - The model package is pending being created.
--
-- -   @IN_PROGRESS@ - The model package is in the process of being
--     created.
--
-- -   @COMPLETED@ - The model package was successfully created.
--
-- -   @FAILED@ - The model package failed.
--
-- -   @DELETING@ - The model package is in the process of being deleted.
modelPackage_modelPackageStatus :: Lens.Lens' ModelPackage (Prelude.Maybe ModelPackageStatus)
modelPackage_modelPackageStatus = Lens.lens (\ModelPackage' {modelPackageStatus} -> modelPackageStatus) (\s@ModelPackage' {} a -> s {modelPackageStatus = a} :: ModelPackage)

-- | Metrics for the model.
modelPackage_modelMetrics :: Lens.Lens' ModelPackage (Prelude.Maybe ModelMetrics)
modelPackage_modelMetrics = Lens.lens (\ModelPackage' {modelMetrics} -> modelMetrics) (\s@ModelPackage' {} a -> s {modelMetrics = a} :: ModelPackage)

-- | Undocumented member.
modelPackage_modelPackageStatusDetails :: Lens.Lens' ModelPackage (Prelude.Maybe ModelPackageStatusDetails)
modelPackage_modelPackageStatusDetails = Lens.lens (\ModelPackage' {modelPackageStatusDetails} -> modelPackageStatusDetails) (\s@ModelPackage' {} a -> s {modelPackageStatusDetails = a} :: ModelPackage)

-- | The time that the model package was created.
modelPackage_creationTime :: Lens.Lens' ModelPackage (Prelude.Maybe Prelude.UTCTime)
modelPackage_creationTime = Lens.lens (\ModelPackage' {creationTime} -> creationTime) (\s@ModelPackage' {} a -> s {creationTime = a} :: ModelPackage) Prelude.. Lens.mapping Core._Time

-- | Undocumented member.
modelPackage_lastModifiedBy :: Lens.Lens' ModelPackage (Prelude.Maybe UserContext)
modelPackage_lastModifiedBy = Lens.lens (\ModelPackage' {lastModifiedBy} -> lastModifiedBy) (\s@ModelPackage' {} a -> s {lastModifiedBy = a} :: ModelPackage)

-- | Undocumented member.
modelPackage_createdBy :: Lens.Lens' ModelPackage (Prelude.Maybe UserContext)
modelPackage_createdBy = Lens.lens (\ModelPackage' {createdBy} -> createdBy) (\s@ModelPackage' {} a -> s {createdBy = a} :: ModelPackage)

-- | The name of the model.
modelPackage_modelPackageName :: Lens.Lens' ModelPackage (Prelude.Maybe Prelude.Text)
modelPackage_modelPackageName = Lens.lens (\ModelPackage' {modelPackageName} -> modelPackageName) (\s@ModelPackage' {} a -> s {modelPackageName = a} :: ModelPackage)

instance Core.FromJSON ModelPackage where
  parseJSON =
    Core.withObject
      "ModelPackage"
      ( \x ->
          ModelPackage'
            Prelude.<$> (x Core..:? "Tags" Core..!= Prelude.mempty)
            Prelude.<*> (x Core..:? "ModelPackageVersion")
            Prelude.<*> (x Core..:? "ModelPackageGroupName")
            Prelude.<*> (x Core..:? "SourceAlgorithmSpecification")
            Prelude.<*> (x Core..:? "ValidationSpecification")
            Prelude.<*> (x Core..:? "CertifyForMarketplace")
            Prelude.<*> (x Core..:? "InferenceSpecification")
            Prelude.<*> (x Core..:? "ModelApprovalStatus")
            Prelude.<*> (x Core..:? "MetadataProperties")
            Prelude.<*> (x Core..:? "ModelPackageDescription")
            Prelude.<*> (x Core..:? "ApprovalDescription")
            Prelude.<*> (x Core..:? "ModelPackageArn")
            Prelude.<*> (x Core..:? "LastModifiedTime")
            Prelude.<*> (x Core..:? "ModelPackageStatus")
            Prelude.<*> (x Core..:? "ModelMetrics")
            Prelude.<*> (x Core..:? "ModelPackageStatusDetails")
            Prelude.<*> (x Core..:? "CreationTime")
            Prelude.<*> (x Core..:? "LastModifiedBy")
            Prelude.<*> (x Core..:? "CreatedBy")
            Prelude.<*> (x Core..:? "ModelPackageName")
      )

instance Prelude.Hashable ModelPackage where
  hashWithSalt _salt ModelPackage' {..} =
    _salt `Prelude.hashWithSalt` tags
      `Prelude.hashWithSalt` modelPackageVersion
      `Prelude.hashWithSalt` modelPackageGroupName
      `Prelude.hashWithSalt` sourceAlgorithmSpecification
      `Prelude.hashWithSalt` validationSpecification
      `Prelude.hashWithSalt` certifyForMarketplace
      `Prelude.hashWithSalt` inferenceSpecification
      `Prelude.hashWithSalt` modelApprovalStatus
      `Prelude.hashWithSalt` metadataProperties
      `Prelude.hashWithSalt` modelPackageDescription
      `Prelude.hashWithSalt` approvalDescription
      `Prelude.hashWithSalt` modelPackageArn
      `Prelude.hashWithSalt` lastModifiedTime
      `Prelude.hashWithSalt` modelPackageStatus
      `Prelude.hashWithSalt` modelMetrics
      `Prelude.hashWithSalt` modelPackageStatusDetails
      `Prelude.hashWithSalt` creationTime
      `Prelude.hashWithSalt` lastModifiedBy
      `Prelude.hashWithSalt` createdBy
      `Prelude.hashWithSalt` modelPackageName

instance Prelude.NFData ModelPackage where
  rnf ModelPackage' {..} =
    Prelude.rnf tags
      `Prelude.seq` Prelude.rnf modelPackageVersion
      `Prelude.seq` Prelude.rnf modelPackageGroupName
      `Prelude.seq` Prelude.rnf sourceAlgorithmSpecification
      `Prelude.seq` Prelude.rnf validationSpecification
      `Prelude.seq` Prelude.rnf certifyForMarketplace
      `Prelude.seq` Prelude.rnf inferenceSpecification
      `Prelude.seq` Prelude.rnf modelApprovalStatus
      `Prelude.seq` Prelude.rnf metadataProperties
      `Prelude.seq` Prelude.rnf modelPackageDescription
      `Prelude.seq` Prelude.rnf approvalDescription
      `Prelude.seq` Prelude.rnf modelPackageArn
      `Prelude.seq` Prelude.rnf lastModifiedTime
      `Prelude.seq` Prelude.rnf modelPackageStatus
      `Prelude.seq` Prelude.rnf modelMetrics
      `Prelude.seq` Prelude.rnf modelPackageStatusDetails
      `Prelude.seq` Prelude.rnf creationTime
      `Prelude.seq` Prelude.rnf lastModifiedBy
      `Prelude.seq` Prelude.rnf createdBy
      `Prelude.seq` Prelude.rnf modelPackageName
