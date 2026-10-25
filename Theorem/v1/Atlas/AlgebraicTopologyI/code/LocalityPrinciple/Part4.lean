/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/LocalityPrinciple.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.SubdivisionSmall.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.SubdivisionSmall
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section13
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Def.v1.Atlas.AlgebraicTopologyI.code.Section13.Part3
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part4


noncomputable section

open CategoryTheory AlgebraicTopologyI Finset BigOperators BarycentricSubdivision

namespace LocalityPrinciple

variable (X : TopCat.{0}) (𝒜 : Set (Set X))

/-- On a single $\mathcal{A}$-small simplex $\sigma$, the homotopy operator $h_k$
produces an $\mathcal{A}$-small chain, since each simplex in its support has image
inside that of $\sigma$. -/
lemma isSmallChain_homotopyOpK_of {X : Type*} [TopologicalSpace X]
    (𝒜 : Set (Set X)) (n : ℕ) (k : ℕ)
    (σ : SingularSimplex n X) (hσ : IsSmall 𝒜 σ) :
    IsSmallChain 𝒜 (homotopyOpK n k (FreeAbelianGroup.of σ)) := by
  show IsSmallChain 𝒜 ((FreeAbelianGroup.lift _) (FreeAbelianGroup.of σ))
  rw [FreeAbelianGroup.lift_apply_of]
  intro τ hτ
  obtain ⟨A, hA, hrange⟩ := hσ
  exact ⟨A, hA, (range_subset_of_mem_support_map
    (show C(↥(stdSimplex ℝ (Fin (n + 1))), X) from σ) _ τ hτ).trans hrange⟩

/-- The homotopy operator $h_k$ sends $\mathcal{A}$-small chains to
$\mathcal{A}$-small chains, so it restricts to the small subcomplex. -/
theorem homotopyOpK_mem_smallChainSubgroup {X : Type*} [TopologicalSpace X]
    (𝒜 : Set (Set X)) (n : ℕ) (k : ℕ)
    (c : SingularChains n X) (hc : c ∈ smallChainSubgroup n 𝒜) :
    homotopyOpK n k c ∈ smallChainSubgroup (n + 1) 𝒜 := by
  have hle : smallChainSubgroup n 𝒜 ≤
      (smallChainSubgroup (n + 1) 𝒜).comap (homotopyOpK n k) := by
    change AddSubgroup.closure _ ≤ _
    rw [AddSubgroup.closure_le]
    intro x ⟨σ, hσ, hx⟩
    subst hx
    show homotopyOpK n k (FreeAbelianGroup.of σ) ∈ smallChainSubgroup (n + 1) 𝒜
    exact isSmallChain_mem_smallChainSubgroup 𝒜 _
      (isSmallChain_homotopyOpK_of 𝒜 n k σ hσ)
  exact hle hc

end LocalityPrinciple
end
