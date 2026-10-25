/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/OppositeConjugacyInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.Buildings.code.GeometricAlgebra.FlagEquivalenceInstance
import Lemma.Submodule.Any_EqMapToLinearMap.of.FinrankK
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.OppositeConjugacyInstance


namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]


/-- Hypothesis bundling the composition step needed for the conjugacy-of-opposite
flags theorem: given a flag `F` and two opposite flags `F'₁, F'₂`, there exists a
linear automorphism preserving `F` and mapping `F'₁` to `F'₂`. -/
structure OppositeConjugacyCompositionHyp (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V] where
  compose_swaps : ∀ (F F'₁ F'₂ : Flag k V),
    Flag.isOppositeFlag F F'₁ →
    Flag.isOppositeFlag F F'₂ →
    ∃ (e : V ≃ₗ[k] V) (hlen : F'₁.len = F'₂.len),
      (∀ i : Fin F.len, (F.spaces i).map e.toLinearMap = F.spaces i) ∧
      (∀ i : Fin F'₁.len, (F'₁.spaces i).map e.toLinearMap = F'₂.spaces (i.cast hlen))

end GeometricAlgebra
