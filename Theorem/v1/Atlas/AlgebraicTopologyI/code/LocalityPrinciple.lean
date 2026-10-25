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
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple


noncomputable section

open CategoryTheory AlgebraicTopologyI Finset BigOperators BarycentricSubdivision

namespace LocalityPrinciple

variable (X : TopCat.{0}) (𝒜 : Set (Set X))

/-- The $i$-th face of an $\mathcal{A}$-small simplex is again $\mathcal{A}$-small,
since its image is a subset of the original simplex's image. -/
lemma isSmall_face {n : ℕ} {X : Type*} [TopologicalSpace X] (𝒜 : Set (Set X))
    (σ : SingularSimplex (n + 1) X) (hσ : IsSmall 𝒜 σ)
    (i : Fin (n + 2)) : IsSmall 𝒜 (SingularSimplex.face i σ) := by
  obtain ⟨A, hA, hrange⟩ := hσ
  exact ⟨A, hA, fun x ⟨t, ht⟩ => hrange ⟨faceInclusion n i t, ht⟩⟩

/-- The singular boundary map sends $\mathcal{A}$-small chains to $\mathcal{A}$-small
chains, so the subcomplex $S_*^{\mathcal{A}}(X)$ is closed under $\partial$. -/
lemma boundaryMap_mem_smallChainSubgroup {n : ℕ} {X : Type*} [TopologicalSpace X]
    (𝒜 : Set (Set X))
    (c : SingularChains (n + 1) X)
    (hc : c ∈ smallChainSubgroup (n + 1) 𝒜) :
    boundaryMap n X c ∈ smallChainSubgroup n 𝒜 := by
  have key : smallChainSubgroup (n + 1) 𝒜 ≤
      (smallChainSubgroup n 𝒜).comap (boundaryMap n X) := by
    unfold smallChainSubgroup
    rw [AddSubgroup.closure_le]
    intro x ⟨σ, hσ, hx⟩
    show boundaryMap n X x ∈ smallChainSubgroup n 𝒜
    subst hx
    change (FreeAbelianGroup.lift (fun σ => ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      FreeAbelianGroup.of (SingularSimplex.face i σ))) (FreeAbelianGroup.of σ) ∈ _
    rw [FreeAbelianGroup.lift_apply_of]
    exact sum_mem (fun i _ => (smallChainSubgroup n 𝒜).zsmul_mem
      (AddSubgroup.subset_closure ⟨SingularSimplex.face i σ, isSmall_face 𝒜 σ hσ i, rfl⟩) _)
  exact key hc

end LocalityPrinciple
end
