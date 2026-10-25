/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DifferentialForms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms
set_option autoImplicit false

attribute [reducible, instance] DifferentialFormSpace.instAddCommGroup
attribute [reducible, instance] DifferentialFormSpace.instModule

attribute [instance] HasComplexScalars.instComplexModule
attribute [instance] HasComplexScalars.instScalarTower
attribute [instance] HasComplexScalars.instSMulCommClass


/-- Marker class for a differential form space modelled on Euclidean space of positive dimension `dim`. -/
class IsEuclideanDFS (Ω : ℕ → Type*) (VF : Type*) [inst : DifferentialFormSpace Ω VF] where
  dim : ℕ
  dim_pos : 0 < dim

