/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DifferentialForms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.GeometryOfManifolds.code.DifferentialForms
set_option autoImplicit false

attribute [reducible, instance] DifferentialFormSpace.instAddCommGroup
attribute [reducible, instance] DifferentialFormSpace.instModule

attribute [instance] HasComplexScalars.instComplexModule
attribute [instance] HasComplexScalars.instScalarTower
attribute [instance] HasComplexScalars.instSMulCommClass


/-- The identity morphism of differential form spaces, with trivial pullback. -/
def DFSMorphism.id {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF] : DFSMorphism Ω VF Ω VF where
  pullback α := α
  pullback_add _ _ := rfl
  pullback_smul _ _ := rfl
  pullback_comm_d _ := rfl

