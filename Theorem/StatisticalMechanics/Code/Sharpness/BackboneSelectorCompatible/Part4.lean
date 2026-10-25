/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2Quantitative
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Def.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part4
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]


theorem shb_support_indicator_eq_sum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {x y : V} (hxy : x ≠ y)
    (m : G.edgeFinset → ℕ) :
    (if sources G (ofEdgeFun G m) = {x, y} then
        weight G β J (ofEdgeFun G m) else 0) =
      ∑ p : G.Path x y,
        if sources G (ofEdgeFun G m) = {x, y} ∧
            shb_backboneSelectSupport G (ofEdgeFun G m) x y = some p then
          weight G β J (ofEdgeFun G m) else 0 := by
  let n := ofEdgeFun G m
  by_cases hs : sources G n = {x, y}
  · rw [if_pos hs]
    have hne : (shb_backboneSet G n x y).Nonempty :=
      shb_backboneSet_nonempty_of_sources G n hxy hs
    have hsel : shb_backboneSelectSupport G n x y =
        some ((@Finset.min' _ (shb_supportPathOrder G x y)
          (shb_backboneSet G n x y) hne)) := by
      unfold shb_backboneSelectSupport
      rw [dif_pos hne]
    letI : LinearOrder (G.Path x y) := shb_supportPathOrder G x y
    let p := (shb_backboneSet G n x y).min' hne
    rw [Finset.sum_eq_single p]
    · rw [if_pos ⟨hs, by simpa [p] using hsel⟩]
    · intro q _ hqp
      rw [if_neg]
      rintro ⟨_, hq⟩
      have : q = p := by
        apply Option.some.inj
        exact hq.symm.trans (by simpa [p] using hsel)
      exact hqp this
    · intro hp
      exact absurd (Finset.mem_univ p) hp
  · rw [if_neg hs]
    symm
    apply Finset.sum_eq_zero
    intro p _
    rw [if_neg]
    exact fun h => hs h.1


theorem shb_currentSum_eq_sum_backboneNumSupport
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) {x y : V} (hxy : x ≠ y) :
    currentSum G β J {x, y} =
      ∑ p : G.Path x y, shb_backboneNumSupport G β J x y p := by
  unfold currentSum shb_backboneNumSupport
  rw [← Summable.tsum_finsetSum (s := (Finset.univ : Finset (G.Path x y)))
    (f := fun p (m : G.edgeFinset → ℕ) =>
      if sources G (ofEdgeFun G m) = {x, y} ∧
          shb_backboneSelectSupport G (ofEdgeFun G m) x y = some p then
        weight G β J (ofEdgeFun G m) else 0)
    (fun p _ => shb_summable_indicator G β J hβ hJ _)]
  exact tsum_congr (fun m => shb_support_indicator_eq_sum G β J hxy m)


theorem shb_P1_support
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) {x y : V} (hxy : x ≠ y) :
    expectationJ G β J {x, y} =
      ∑ p : G.Path x y, shb_rhoSupport G β J x y p := by
  rw [current_representation,
    shb_currentSum_eq_sum_backboneNumSupport G β J hβ hJ hxy]
  unfold shb_rhoSupport
  rw [Finset.sum_div]


end StatMech.Sharpness
