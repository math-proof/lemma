/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/OppositeConjugacyInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.Buildings.code.GeometricAlgebra.FlagEquivalenceInstance
import Lemma.Submodule.Any_EqMapToLinearMap.of.FinrankK
import Structure.v1.Atlas.Buildings.code.GeometricAlgebra.OppositeConjugacyInstance


namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]


/-- The conjugacy theorem for opposite flags: given the composition hypothesis,
any two flags opposite to `F` are conjugate by a linear automorphism that fixes
the spaces of `F`. -/
theorem opposite_systems_conjugacy_theorem (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hyp : OppositeConjugacyCompositionHyp k V)
    (F F'₁ F'₂ : Flag k V)
    (h₁ : Flag.isOppositeFlag F F'₁)
    (h₂ : Flag.isOppositeFlag F F'₂) :
    ∃ (e : V ≃ₗ[k] V) (hlen : F'₁.len = F'₂.len),
      (∀ i : Fin F.len, (F.spaces i).map e.toLinearMap = F.spaces i) ∧
      (∀ i : Fin F'₁.len, (F'₁.spaces i).map e.toLinearMap = F'₂.spaces (i.cast hlen)) :=
  hyp.compose_swaps F F'₁ F'₂ h₁ h₂

end GeometricAlgebra
