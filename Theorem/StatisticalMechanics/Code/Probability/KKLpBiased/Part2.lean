/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.TwoDim.KKLWire.Part2
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
import Def.StatisticalMechanics.Code.Probability.KKLpBiased.Part2
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Probability

open ConfigSpace Function Finset StatMech StatMech.OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem kpb_residue_c0 {q : ℝ} (hq : q ≤ 1) :
    ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, KKLHypercontractive p 0 := by
  intro p hp
  exact kkl_hypercontractive_zero p (by linarith [hp.1]) (by linarith [hp.2])


theorem kpb_PBiasedHC_half_holds : KKLHypercontractive (1 / 2 : ℝ) 2 :=
  bph_KKL cro2_rhoOptimise


theorem kpb_residue_noncirc {p : ℝ} (H : KKLHypercontractive p 2)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    2 * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p)
            (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  H φ


theorem kpb_kkl_pbiased {q : ℝ} (Hpb : kpb_PBiasedHC q) :
    ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, KKLHypercontractive p 2 :=
  Hpb


theorem kpb_Hbkkkl {q : ℝ} (Hpb : kpb_PBiasedHC q) :
    ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), KKLHypercontractive p 2 := by
  intro p hp
  rw [interior_Icc] at hp
  exact Hpb p hp


theorem kpb_sharpThreshold {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] (hA : IsIncreasing A)
    {q v₀ L : ℝ} (hq : (1 : ℝ) / 2 ≤ q)
    (hv0 : 0 ≤ v₀) (hL : 0 ≤ L)
    (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
    (Hpb : kpb_PBiasedHC q)
    (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
    (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      L ≤ StatMech.TwoDim.kklw_logMaxInfl p A) :
    1 / 2 + (2 * v₀ * L) * (q - 1 / 2) ≤ StatMech.prob q A :=
  StatMech.TwoDim.kklw_sharpThreshold A hA hq hv0 hL hhalf (kpb_Hbkkkl Hpb) hvar hLL'


theorem kpb_sharpThreshold_window {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] (hA : IsIncreasing A)
    {q v₀ L ε : ℝ} (hq : (1 : ℝ) / 2 ≤ q)
    (hM : 0 < 2 * v₀ * L)
    (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
    (hv0 : 0 ≤ v₀) (hL : 0 ≤ L)
    (Hpb : kpb_PBiasedHC q)
    (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
    (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      L ≤ StatMech.TwoDim.kklw_logMaxInfl p A)
    (hnotyet : StatMech.prob q A ≤ 1 - ε) :
    q - 1 / 2 ≤ (1 / 2 - ε) / (2 * v₀ * L) :=
  StatMech.TwoDim.kklw_sharpThreshold_window A hA hq hM hhalf hv0 hL (kpb_Hbkkkl Hpb)
    hvar hLL' hnotyet

end Probability
end StatMech
