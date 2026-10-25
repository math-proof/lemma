/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteHardField.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Def.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField.Part2
open Filter
open scoped BigOperators Topology


namespace StatMech

namespace Exact3D

theorem boundaryGhostMismatchCount_eq_zero_iff (d n : ℕ)
    (σ : BoundaryGhostConfig d n) :
    boundaryGhostMismatchCount d n σ = 0 ↔
      ∀ x : FK.boxVerts d n, FK.boxBoundary d n x →
        σ (some x) = σ none := by
  classical
  unfold boundaryGhostMismatchCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h x hx
    by_contra hne
    exact h (Finset.mem_univ x) ⟨hx, hne⟩
  · intro h x _hx hxbad
    exact hxbad.2 (h x hxbad.1)


theorem boundaryGhost_bond_some_none_eq_if
    {V : Type*} (σ : ConfigSpace (Option V)) (x : V) :
    Ising.bond σ s(some x, none) =
      if σ (some x) = σ none then 1 else -1 := by
  rw [Ising.bond_mk]
  unfold Ising.spin
  by_cases h : σ (some x) = σ none
  · rw [if_pos h]
    cases hnone : σ none <;> cases hsome : σ (some x) <;> simp_all
  · rw [if_neg h]
    cases hnone : σ none <;> cases hsome : σ (some x) <;> simp_all


theorem finset_sum_ite_neg_one_eq_card_sub_two_filter
    {α : Type*} (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (∑ x ∈ s, if p x then (-1 : ℝ) else 1) =
      (s.card : ℝ) - 2 * ((s.filter p).card : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s has ih =>
      by_cases hp : p a
      · simp [Finset.filter_insert, has, hp, ih]
        ring
      · simp [Finset.filter_insert, has, hp, ih]
        ring


theorem boundaryGhost_boundaryBondSum_eq_card_sub_two_mismatch
    (d n : ℕ) (σ : BoundaryGhostConfig d n) :
    (∑ x ∈ (Finset.univ.filter (FK.boxBoundary d n)),
        Ising.bond σ s(some x, none)) =
      (((Finset.univ.filter (FK.boxBoundary d n)).card : ℝ) -
        2 * (boundaryGhostMismatchCount d n σ : ℝ)) := by
  classical
  let bdrySet : Finset (FK.boxVerts d n) :=
    Finset.univ.filter (FK.boxBoundary d n)
  let bad : FK.boxVerts d n → Prop := fun x => σ (some x) ≠ σ none
  have hterm :
      ∀ x, Ising.bond σ s(some x, none) =
        if bad x then (-1 : ℝ) else 1 := by
    intro x
    rw [boundaryGhost_bond_some_none_eq_if]
    by_cases hx : σ (some x) = σ none
    · simp [bad, hx]
    · simp [bad, hx]
  calc
    (∑ x ∈ (Finset.univ.filter (FK.boxBoundary d n)),
        Ising.bond σ s(some x, none))
        = ∑ x ∈ bdrySet, if bad x then (-1 : ℝ) else 1 := by
          refine Finset.sum_congr ?_ ?_
          · rfl
          · intro x _hx
            rw [hterm x]
    _ = (bdrySet.card : ℝ) - 2 * ((bdrySet.filter bad).card : ℝ) := by
          exact finset_sum_ite_neg_one_eq_card_sub_two_filter bdrySet bad
    _ = (((Finset.univ.filter (FK.boxBoundary d n)).card : ℝ) -
        2 * (boundaryGhostMismatchCount d n σ : ℝ)) := by
          simp [bdrySet, bad, boundaryGhostMismatchCount,
            Finset.filter_filter]


theorem boundaryGhost_weightedBondSum_split
    (d n : ℕ) (H : ℝ) (σ : BoundaryGhostConfig d n) :
    (∑ e ∈ (Sharpness.withGhost (FK.boxGraph d n)).edgeFinset,
        boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1) e *
          Ising.bond σ e)
      =
      (∑ e ∈ (FK.boxGraph d n).edgeFinset,
          (1 : ℝ) * Ising.bond (fun x => σ (some x)) e)
        + H * ∑ x ∈ (Finset.univ.filter (FK.boxBoundary d n)),
          Ising.bond σ s(some x, none) := by
  classical
  rw [Sharpness.FieldGhostDict.withGhost_edgeFinset_eq,
    Finset.sum_union
      (Sharpness.FieldGhostDict.disjoint_orig_ghost (FK.boxGraph d n))]
  congr 1
  · rw [Sharpness.FieldGhostDict.origEdges, Finset.sum_image]
    · refine Finset.sum_congr rfl (fun e _ => ?_)
      induction e with
      | h x y =>
          rw [Sym2.map_mk, Ising.bond_mk, Ising.bond_mk]
          simp only [boundaryGhostCoupling_some_some, one_mul]
          unfold Ising.spin
          rfl
    · intro a _ b _ hab
      exact Sym2.map.injective (Option.some_injective (FK.boxVerts d n)) hab
  · rw [Sharpness.FieldGhostDict.ghostEdges, Finset.sum_image]
    · rw [Finset.mul_sum]
      calc
        (∑ x : FK.boxVerts d n,
            boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1)
                s(some x, none) *
              Ising.bond σ s(some x, none))
            = ∑ x : FK.boxVerts d n,
                if FK.boxBoundary d n x then
                  H * Ising.bond σ s(some x, none)
                else 0 := by
              refine Finset.sum_congr rfl (fun x _ => ?_)
              by_cases hx : FK.boxBoundary d n x <;> simp [hx]
        _ = ∑ x ∈ (Finset.univ.filter (FK.boxBoundary d n)),
              H * Ising.bond σ s(some x, none) := by
              rw [← Finset.sum_filter]
    · intro a _ b _ hab
      rw [Sym2.eq_iff] at hab
      rcases hab with ⟨h1, _⟩ | ⟨_h1, h2⟩
      · exact Option.some_injective (FK.boxVerts d n) h1
      · exact absurd h2 (by simp)


theorem boundaryGhost_weightedBondSum_eq_original_add_mismatch
    (d n : ℕ) (H : ℝ) (σ : BoundaryGhostConfig d n) :
    (∑ e ∈ (Sharpness.withGhost (FK.boxGraph d n)).edgeFinset,
        boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1) e *
          Ising.bond σ e)
      =
      (∑ e ∈ (FK.boxGraph d n).edgeFinset,
          (1 : ℝ) * Ising.bond (fun x => σ (some x)) e)
        + H * (((Finset.univ.filter (FK.boxBoundary d n)).card : ℝ) -
          2 * (boundaryGhostMismatchCount d n σ : ℝ)) := by
  rw [boundaryGhost_weightedBondSum_split,
    boundaryGhost_boundaryBondSum_eq_card_sub_two_mismatch]


end Exact3D
end StatMech
