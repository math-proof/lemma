/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SharpThresholdWire.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.HCTensorLib
import Theorem.StatisticalMechanics.Code.Probability.PBiasedHCLib.Part3
import Def.StatisticalMechanics.Code.Probability.SharpThresholdWire
open scoped BigOperators
open Finset
open Real Set
open StatMech StatMech.OSSS

set_option linter.style.longLine false


namespace StatMech.Probability

theorem stw_rhoOptimise_of_lib {q : ℝ} (H : stw_RemainingGoal q) :
    ptn_RhoOptimise q :=
  htl_rhoOptimise_of_lib H


theorem stw_sharpThreshold_of_lib {q : ℝ} (hq1 : q ≤ 1)
    (H : stw_RemainingGoal q)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] (hA : IsIncreasing A)
    {v₀ L : ℝ} (hq : (1 : ℝ) / 2 ≤ q) (hv0 : 0 ≤ v₀) (hL : 0 ≤ L)
    (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
    (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
    (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      L ≤ StatMech.TwoDim.kklw_logMaxInfl p A) :
    1 / 2 + (2 * v₀ * L) * (q - 1 / 2) ≤ StatMech.prob q A :=
  htl_sharpThreshold hq1 H A hA hq hv0 hL hhalf hvar hLL'


theorem stw_RemainingGoal_empty_window {q : ℝ} (hq : q ≤ 1 / 2) : stw_RemainingGoal q := by
  intro p hp
  exact absurd (lt_trans hp.1 hp.2) (by linarith [hq] : ¬ (1 / 2 : ℝ) < q)


theorem stw_verdict {u p : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hne : p ≠ 1 / 2) :
    (1 < 2 - u ∧ 2 - u ≤ 2) ∧ (4 * p ^ 2 * (1 - p) ^ 2 < p * (1 - p)) := by
  refine ⟨stw_master_uses_exponent_le_two hu0 hu1, ?_⟩
  rcases lt_or_ge (4 * p ^ 2 * (1 - p) ^ 2) (p * (1 - p)) with h | h
  · exact h
  · exact absurd (le_antisymm (stw_variance_coeff_gap hp0.le hp1.le) h)
      (fun heq => hne ((stw_coeff_gap_eq_iff_half hp0 hp1).mp heq))

end StatMech.Probability
