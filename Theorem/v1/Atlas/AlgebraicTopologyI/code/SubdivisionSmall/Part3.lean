/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Algebra.Order.Archimedean.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.SubdivisionSmall.Part2


noncomputable section

namespace AlgebraicTopologyI

variable {X : Type*} [TopologicalSpace X]

/-- The iterated subdivision operator is additive. -/
lemma iterateSubdivision_add {n : ℕ}
    (k : ℕ) (a b : SingularChains n X) :
    iterateSubdivision k (a + b) =
    iterateSubdivision k a + iterateSubdivision k b :=
  iterate_map_add (subdivisionOp n X) k a b

/-- Every singular simplex appearing in the support of `SingularChains.map σ c` has image
contained in the range of `σ`. -/
lemma range_subset_of_mem_support_map {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {n : ℕ} (σ : C(Y, Z)) (c : SingularChains n Y)
    (τ : SingularSimplex n Z)
    (hτ : τ ∈ FreeAbelianGroup.support (SingularChains.map σ c)) :
    Set.range (show C(↥(stdSimplex ℝ (Fin (n + 1))), Z) from τ) ⊆ Set.range σ := by
  simp only [SingularChains.map] at hτ
  have hmap :
      τ ∈ ((FreeAbelianGroup.lift (FreeAbelianGroup.of ∘ SingularSimplex.map σ)) c).support :=
    hτ
  exact lift_support_forall (FreeAbelianGroup.of ∘ SingularSimplex.map σ) c
    (fun τ => Set.range (show C(↥(stdSimplex ℝ (Fin (n + 1))), Z) from τ) ⊆ Set.range σ)
    (fun ρ _ τ' hτ' => by
      simp only [Function.comp, FreeAbelianGroup.support_of, Finset.mem_singleton] at hτ'
      subst hτ'
      simp only [SingularSimplex.map]
      exact Set.range_comp_subset_range
        (show C(↥(stdSimplex ℝ (Fin (n + 1))), Y) from ρ) σ)
    τ hmap

/-- The subdivision operator preserves `𝒜`-smallness: if `c` is `𝒜`-small then so is
`$c`. -/
lemma isSmallChain_subdivisionOp {𝒜 : Set (Set X)} {n : ℕ} {c : SingularChains n X}
    (h : IsSmallChain 𝒜 c) :
    IsSmallChain 𝒜 (subdivisionOp n X c) := by
  intro τ hτ
  exact lift_support_forall
    (fun σ : SingularSimplex n X => SingularChains.map σ (stdSubdivisionChain n))
    c (fun τ => IsSmall 𝒜 τ)
    (fun σ hσ τ' hτ' => by
      obtain ⟨A, hA, hrange⟩ := h σ hσ
      exact ⟨A, hA, (range_subset_of_mem_support_map σ _ τ' hτ').trans hrange⟩)
    τ hτ

/-- If the `k`-th iterate of the subdivision operator applied to `c` is `𝒜`-small, then
so is the `(k+1)`-th iterate. -/
lemma isSmallChain_iterateSubdivision_succ {𝒜 : Set (Set X)} {n : ℕ}
    {c : SingularChains n X} {k : ℕ}
    (h : IsSmallChain 𝒜 (iterateSubdivision k c)) :
    IsSmallChain 𝒜 (iterateSubdivision (k + 1) c) := by
  show IsSmallChain 𝒜 ((⇑(subdivisionOp n X))^[k + 1] c)
  rw [Function.iterate_succ']
  exact isSmallChain_subdivisionOp h

/-- Monotonicity: once an iterate of the subdivision operator applied to `c` is
`𝒜`-small, all subsequent iterates remain `𝒜`-small. -/
lemma isSmallChain_iterateSubdivision_mono {𝒜 : Set (Set X)} {n : ℕ}
    {c : SingularChains n X} {k : ℕ}
    (h : IsSmallChain 𝒜 (iterateSubdivision k c)) (j : ℕ) :
    IsSmallChain 𝒜 (iterateSubdivision (k + j) c) := by
  induction j with
  | zero => rwa [Nat.add_zero]
  | succ j ih =>
    have : k + (j + 1) = (k + j) + 1 := by omega
    rw [this]
    exact isSmallChain_iterateSubdivision_succ ih

end AlgebraicTopologyI
end
