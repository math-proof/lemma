/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.Comparison
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Def.StatisticalMechanics.Code.FK.FiniteEnergy.Part3
open scoped BigOperators
open Module SimpleGraph


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem cFE_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) : 0 < cFE p q := by
  unfold cFE
  apply lt_min
  · apply div_pos hp; nlinarith
  · linarith


theorem cFE_le_half {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) : cFE p q ≤ 1 / 2 := by
  unfold cFE
  rcases le_or_gt p (1 / 2) with h | h
  · refine le_trans (min_le_left _ _) ?_
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  · exact le_trans (min_le_right _ _) (by linarith)


theorem finite_energy {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) :
    cFE p q ≤ condOpen G p q e ω ∧ condOpen G p q e ω ≤ 1 - cFE p q := by
  by_cases he : e ∈ G.edgeFinset
  · rw [condOpen_eq_weightRatio G hp hp1 (by linarith)]
    set W1 := fkWeight G p q (setOpen e ω) with hW1
    set W0 := fkWeight G p q (setClosed e ω) with hW0
    have hW1pos : 0 < W1 := fkWeight_pos G hp hp1 (by linarith) _
    have hW0pos : 0 < W0 := fkWeight_pos G hp hp1 (by linarith) _
    have hlo : (1 - p) * W1 ≤ p * W0 := fkWeight_lo G hp hp1 hq he ω
    have hhi : p * W0 ≤ q * (1 - p) * W1 := fkWeight_hi G hp hp1 hq he ω
    have hsum : 0 < W1 + W0 := by linarith
    have hden2 : 0 < p + q * (1 - p) := by nlinarith
    have hub : W1 / (W1 + W0) ≤ p := by rw [div_le_iff₀ hsum]; nlinarith
    have hlb : p / (p + q * (1 - p)) ≤ W1 / (W1 + W0) := by
      rw [div_le_div_iff₀ hden2 hsum]; nlinarith
    refine ⟨le_trans (min_le_left _ _) hlb, ?_⟩
    have hgap : 1 - cFE p q ≥ p := by
      unfold cFE
      have := min_le_right (p / (p + q * (1 - p))) (1 - p)
      linarith
    linarith
  · rw [condOpen_eq_half G hp hp1 (by linarith) he]
    have hc := cFE_le_half hp hp1 hq
    exact ⟨hc, by linarith⟩

end FK
end StatMech
