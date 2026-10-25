/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedConvexity.Part2
import Theorem.StatisticalMechanics.Code.Probability.KKLpBiased.Part2
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
import Def.StatisticalMechanics.Code.Probability.PBiasedTensorize.Part11
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem ptn_rhoOptimise_hyp_holds {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → ∀ q' : ℝ, 1 ≤ q' → q' ≤ 2 → ρ ^ 2 = (q' - 1) * 4 * p * (1 - p) →
      (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset E, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q' - 1)
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  intro ρ h0 h1 q' hq1 hq2 hρsq
  exact ptn_capped_hc hp0 hp1 h0 h1 hq1 hq2 hρsq φ


theorem ptn_kklHC_of_rhoOptimise {q : ℝ} (H : ptn_RhoOptimise q)
    {p : ℝ} (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1) :
    KKLHypercontractive p 2 := by
  have hp0 : 0 < p := by have := hp.1; linarith
  intro E _ _ _ φ
  exact H p hp hp1 φ (ptn_rhoOptimise_hyp_holds hp0 hp1 φ)


theorem ptn_PBiasedHC_of_rhoOptimise {q : ℝ} (hq : q ≤ 1) (H : ptn_RhoOptimise q) :
    kpb_PBiasedHC q :=
  fun p hp => ptn_kklHC_of_rhoOptimise H hp (by have := hp.2; linarith)


theorem ptn_rhoOptimise_c0 {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    (0 : ℝ) * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  rw [zero_mul, zero_mul]
  exact kkl_totalInfl_nonneg (bernoulliWeight_isProbWeight hp0 hp1) _


theorem ptn_residue_noncirc {q : ℝ} (H : ptn_RhoOptimise q) {p : ℝ}
    (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    2 * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  ptn_kklHC_of_rhoOptimise H hp hp1 φ


theorem ptn_sharpThreshold_of_rhoOptimise {q : ℝ} (hq1 : q ≤ 1) (H : ptn_RhoOptimise q)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] (hA : IsIncreasing A)
    {v₀ L : ℝ} (hq : (1 : ℝ) / 2 ≤ q) (hv0 : 0 ≤ v₀) (hL : 0 ≤ L)
    (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
    (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
    (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      L ≤ StatMech.TwoDim.kklw_logMaxInfl p A) :
    1 / 2 + (2 * v₀ * L) * (q - 1 / 2) ≤ StatMech.prob q A :=
  kpb_sharpThreshold A hA hq hv0 hL hhalf (ptn_PBiasedHC_of_rhoOptimise hq1 H) hvar hLL'

end StatMech.Probability
