/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePropsFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Def.StatisticalMechanics.Code.Sharpness.BackbonePropsFull.Part5
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

open StatMech.Ising (bond)

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem shb_indicator_eq_sum (β : ℝ) (J : Sym2 V → ℝ) {x y : V} (hxy : x ≠ y)
    (m : ↥G.edgeFinset → ℕ) :
    (if Sharpness.sources G (ofEdgeFun G m) = {x, y} then weight G β J (ofEdgeFun G m) else 0)
      = ∑ ω : G.Path x y,
          (if Sharpness.sources G (ofEdgeFun G m) = {x, y}
              ∧ shb_backboneSelect G (ofEdgeFun G m) x y = some ω then
            weight G β J (ofEdgeFun G m) else 0) := by
  set n := ofEdgeFun G m
  by_cases hs : Sharpness.sources G n = {x, y}
  · rw [if_pos hs]
    have hne : (shb_backboneSet G n x y).Nonempty :=
      shb_backboneSet_nonempty_of_sources G n hxy hs
    have hsel : shb_backboneSelect G n x y = some ((shb_backboneSet G n x y).min' hne) := by
      unfold shb_backboneSelect; rw [dif_pos hne]
    rw [Finset.sum_eq_single ((shb_backboneSet G n x y).min' hne)]
    · rw [if_pos ⟨hs, hsel⟩]
    · intro ω _ hne'
      rw [if_neg]
      rintro ⟨_, hsel'⟩
      rw [hsel] at hsel'
      exact hne' ((Option.some.injEq _ _).mp hsel').symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hs]
    refine (Finset.sum_eq_zero ?_).symm
    intro ω _
    rw [if_neg (fun h => hs h.1)]


theorem shb_currentSum_eq_sum_backboneNum (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) {x y : V} (hxy : x ≠ y) :
    currentSum G β J {x, y} = ∑ ω : G.Path x y, shb_backboneNum G β J x y ω := by
  unfold currentSum shb_backboneNum
  rw [← Summable.tsum_finsetSum (s := (Finset.univ : Finset (G.Path x y)))
        (f := fun ω (m : ↥G.edgeFinset → ℕ) =>
          if Sharpness.sources G (ofEdgeFun G m) = {x, y}
              ∧ shb_backboneSelect G (ofEdgeFun G m) x y = some ω then
            weight G β J (ofEdgeFun G m) else 0)
        (fun ω _ => shb_summable_indicator G β J hβ hJ _)]
  refine tsum_congr (fun m => ?_)
  exact shb_indicator_eq_sum G β J hxy m


theorem shb_P1 (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    {x y : V} (hxy : x ≠ y) :
    expectationJ G β J {x, y} = ∑ ω : G.Path x y, shb_rho G β J x y ω := by
  rw [current_representation, shb_currentSum_eq_sum_backboneNum G β J hβ hJ hxy]
  unfold shb_rho
  rw [Finset.sum_div]


theorem shb_P1_ising (β : ℝ) (hβ : 0 ≤ β) {x y : V} (hxy : x ≠ y) :
    StatMech.Ising.isingExpectation G β 0 (StatMech.Ising.spinProd {x, y})
      = ∑ ω : G.Path x y, shb_rho G β (fun _ => 1) x y ω := by
  rw [← expectationJ_one_eq_isingExpectation]
  exact shb_P1 G β (fun _ => 1) hβ (fun _ => zero_le_one) hxy


end Sharpness
end StatMech
