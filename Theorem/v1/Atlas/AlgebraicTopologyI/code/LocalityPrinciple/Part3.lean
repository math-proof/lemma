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
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part3


noncomputable section

open CategoryTheory AlgebraicTopologyI Finset BigOperators BarycentricSubdivision

namespace LocalityPrinciple

variable (X : TopCat.{0}) (𝒜 : Set (Set X))

/-- Iterated subdivision preserves the property of being an $\mathcal{A}$-small
chain. -/
lemma isSmallChain_iterateSubdivision {X : Type*} [TopologicalSpace X]
    {𝒜 : Set (Set X)} {n : ℕ} {c : SingularChains n X}
    (h : IsSmallChain 𝒜 c) (k : ℕ) : IsSmallChain 𝒜 (iterateSubdivision k c) := by
  have h0 : IsSmallChain 𝒜 (iterateSubdivision 0 c) := h
  have := isSmallChain_iterateSubdivision_mono h0 k
  rwa [Nat.zero_add] at this

/-- The iterated subdivision $\mathrm{Sd}^k$ sends $\mathcal{A}$-small chains to
$\mathcal{A}$-small chains, so it restricts to the subcomplex
$S_*^{\mathcal{A}}(X)$. -/
lemma iterateSubdivision_mem_smallChainSubgroup {X : Type*} [TopologicalSpace X]
    (𝒜 : Set (Set X)) (n : ℕ) (k : ℕ)
    (c : SingularChains n X) (hc : c ∈ smallChainSubgroup n 𝒜) :
    iterateSubdivision k c ∈ smallChainSubgroup n 𝒜 := by
  have hle : smallChainSubgroup n 𝒜 ≤
      (smallChainSubgroup n 𝒜).comap (iterateSubdivisionHom n k) := by
    change AddSubgroup.closure _ ≤ _
    rw [AddSubgroup.closure_le]
    intro x ⟨σ, hσ, hx⟩
    subst hx
    show iterateSubdivisionHom n k (FreeAbelianGroup.of σ) ∈ smallChainSubgroup n 𝒜
    change iterateSubdivision k (FreeAbelianGroup.of σ) ∈ smallChainSubgroup n 𝒜
    have hsmall_chain : IsSmallChain 𝒜 (FreeAbelianGroup.of σ) := by
      intro τ hτ
      simp only [supportOfChain, FreeAbelianGroup.support_of, Finset.mem_singleton] at hτ
      rw [hτ]; exact hσ
    exact isSmallChain_mem_smallChainSubgroup 𝒜 _
      (isSmallChain_iterateSubdivision hsmall_chain k)
  exact hle hc

end LocalityPrinciple
end
