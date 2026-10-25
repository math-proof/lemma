/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCoefficientInduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.SpinWeightedBase
import Def.StatisticalMechanics.Code.Onsager.SpinCoefficientInduction


namespace StatMech.Onsager

open Matrix BigOperators StatMech.Ising

theorem norm_ons_restrictEdgeWeight_le
    {L : ℕ} (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (S : Finset (Sym2 (ZMod L × ZMod L))) (q : ℝ) (hq : 0 ≤ q)
    (hweight : ∀ edge, ‖weight edge‖ ≤ q) (edge) :
    ‖ons_restrictEdgeWeight weight S edge‖ ≤ q := by
  unfold ons_restrictEdgeWeight
  split
  · exact hweight edge
  · simpa using hq

theorem ons_scale_restrict_insert_one
    {L : ℕ} (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (S : Finset (Sym2 (ZMod L × ZMod L)))
    (edge : Sym2 (ZMod L × ZMod L)) :
    ons_scaleEdgeWeight (ons_restrictEdgeWeight weight (insert edge S)) edge 1 =
      ons_restrictEdgeWeight weight (insert edge S) := by
  funext f
  simp only [ons_scaleEdgeWeight]
  split <;> ring

theorem ons_scale_restrict_insert_zero
    {L : ℕ} (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (S : Finset (Sym2 (ZMod L × ZMod L)))
    (edge : Sym2 (ZMod L × ZMod L)) (hedge : edge ∉ S) :
    ons_scaleEdgeWeight (ons_restrictEdgeWeight weight (insert edge S)) edge 0 =
      ons_restrictEdgeWeight weight S := by
  funext f
  unfold ons_scaleEdgeWeight ons_restrictEdgeWeight
  by_cases hfe : f = edge
  · subst f
    simp [hedge]
  · simp [hfe]

theorem ons_KWmatWeightedPhase_restrict_edgeFinset
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (omega u v : ℂ) :
    ons_KWmatWeightedPhase L
        (ons_restrictEdgeWeight weight (onsTorusGraph L).edgeFinset) omega u v =
      ons_KWmatWeightedPhase L weight omega u v := by
  ext d2 d1
  unfold ons_KWmatWeightedPhase ons_KWmatWeighted ons_restrictEdgeWeight
  rw [if_pos (ons_portEdge_mem_edgeFinset L d1)]

theorem ons_weightedSpinCharacterSum_restrict_edgeFinset
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (a b : Fin 2) :
    ons_weightedSpinCharacterSum L
        (ons_restrictEdgeWeight weight (onsTorusGraph L).edgeFinset) a b =
      ons_weightedSpinCharacterSum L weight a b := by
  unfold ons_weightedSpinCharacterSum
  apply Finset.sum_congr rfl
  intro F hF
  apply congrArg ((ons_spinCharacter a b (ons_evenHomology L F) : ℂ) * ·)
  apply Finset.prod_congr rfl
  intro edge hedge
  have hdata := hF
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hdata
  simp [ons_restrictEdgeWeight, hdata.1 hedge]


end StatMech.Onsager
