/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderFrame.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.JordanHolderPermutation.Part3
import Lemma.Fin.LeFinrank.of.Le.GtVal_0
import Lemma.Fin.GapVector.in.Spaces.of.LtVal_Val.IsStrictFlag
import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.RefinementCompatibility
import Def.v1.Atlas.Buildings.code.SphericalBuilding.JordanHolderFrame.Part2
set_option maxHeartbeats 800000


namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

/-- The Jordan-Hölder frame is compatible with the flag $\sigma$: each subspace $V_i$ of
$\sigma$ is a sum of frame lines, namely $V_i = \bigoplus_{j < i} k \cdot \ell_j$. -/
theorem jordanHolderFrame_compatible_sigma (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag) [FiniteDimensional k (Vec k n)]
    (i : Fin (n + 1)) :
    (jordanHolderFrame σ τ hσ hτ).IsCompatible k n (σ.spaces i) := by
  use sigmaWitness i
  have hFD : FiniteDimensional k ↥(σ.spaces i) :=
    FiniteDimensional.finiteDimensional_submodule (σ.spaces i)
  symm
  apply biSup_span_singleton_eq_of_le_of_finrank (jhLine_linearIndependent σ τ hσ hτ)
  · apply iSup_le; intro j; apply iSup_le; intro hj
    simp only [sigmaWitness, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    show k ∙ jhLine σ τ hσ hτ j ≤ σ.spaces i
    rw [Submodule.span_singleton_le_iff_mem]
    exact jhLine_mem_of_le σ τ hσ hτ j i (by omega)
  · rw [hσ i, card_sigmaWitness_eq]

end GLnBuilding
