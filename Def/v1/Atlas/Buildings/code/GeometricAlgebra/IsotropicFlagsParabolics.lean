/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/IsotropicFlagsParabolics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
import Lemma.Submodule.OfEq.eq.M.of.Eq
import Lemma.Fin.Eq.of.Ne_0.All_Eq
import Lemma.Submodule.Any_EqMapToLinearMap.of.FinrankK
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.WittTheorem.Part2
import Instance.v1.Atlas.Buildings.code.GeometricAlgebra.FlagEquivalenceInstance


namespace Garrett

variable {k : Type*} [Field k] [DecidableEq k] [NeZero (2 : k)]
  {V : Type*} [AddCommGroup V] [Module k V]


/-- A linear automorphism `Φ : V ≃ₗ V` is a global isometry of the bilinear form
`B` if it preserves all values of `B`. -/
def IsGlobalIsometry (B : LinearMap.BilinForm k V) (Φ : V ≃ₗ[k] V) : Prop :=
  ∀ v₁ v₂ : V, B (Φ v₁) (Φ v₂) = B v₁ v₂


end Garrett
