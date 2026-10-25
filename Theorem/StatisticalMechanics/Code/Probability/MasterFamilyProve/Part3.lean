/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.VarGapProve2
import Theorem.StatisticalMechanics.Code.Probability.PBiasedTwoPoint.Part3
import Def.StatisticalMechanics.Code.Probability.MasterFamilyProve.Part2
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem mfp_kkl_logGain_of_masterFamily {q : ℝ} (H : mfp_masterFamily q)
    {p : ℝ} (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    2 * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
          * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  vgp2_kkl_logGain_of_master H hp hp1 φ


theorem mfp_martingaleHC_of_masterFamily {q : ℝ} (H : mfp_masterFamily q) :
    mxd_martingaleHC_statement q :=
  frh_martingaleHC_of_openResidue H


theorem mfp_kesten_of_masterFamily {q : ℝ} (H : mfp_masterFamily q)
    {p : ℝ} (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1) :
    KKLHypercontractive p 2 :=
  ptn_kklHC_of_rhoOptimise (mxd_rhoOptimise_of_martingaleHC (mfp_martingaleHC_of_masterFamily H)) hp hp1


theorem mfp_masterFamily_half [Nonempty ι] (φ : ConfigSpace ι → Bool) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  hcq_smallDelta_p_half φ hu0 hu1


theorem mfp_masterFamily_nonvacuous {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) (u : ℝ) :
    (0 : ℝ)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  apply mul_nonneg
  · exact Real.rpow_nonneg (kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0 hp1) _) _
  · exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0 hp1) _


theorem mfp_masterFamily_noncirc {q : ℝ} (H : mfp_masterFamily q)
    {p : ℝ} (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  H p hp hp1 φ u hu0 hu1

end StatMech.Probability
