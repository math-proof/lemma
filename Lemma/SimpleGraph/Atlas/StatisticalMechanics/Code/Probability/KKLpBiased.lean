import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.KKLpBiased
open MeasureTheory Set Filter Topology StatMech StatMech.Probability


/--
[kpb_flipAll_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean)
-/
@[path]
private lemma kpb_flipAll_involutive_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  Function.Involutive (kpb_flipAll (E := E)) := by
-- proof
  apply StatMech.Probability.kpb_flipAll_involutive

/--
[kpb_weight_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean)
-/
@[path]
private lemma kpb_weight_flip_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {ω : ConfigSpace E} :
-- imply
  OSSS.weight (OSSS.bernoulliWeight (1 - p)) (kpb_flipAll ω) = OSSS.weight (OSSS.bernoulliWeight p) ω := by
-- proof
  apply StatMech.Probability.kpb_weight_flip p ω

/--
[kpb_expect_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean)
-/
@[path]
private lemma kpb_expect_flip_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {g : ConfigSpace E → ℝ} :
-- imply
  OSSS.expect (OSSS.bernoulliWeight (1 - p)) g = OSSS.expect (OSSS.bernoulliWeight p) (fun ω => g (kpb_flipAll ω)) := by
-- proof
  apply StatMech.Probability.kpb_expect_flip p g

/--
[kpb_flipAll_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean)
-/
@[path]
private lemma kpb_flipAll_setOpen_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  kpb_flipAll (StatMech.setOpen e ω) = StatMech.setClosed e (kpb_flipAll ω) := by
-- proof
  apply StatMech.Probability.kpb_flipAll_setOpen e ω

/--
[kpb_flipAll_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean)
-/
@[path]
private lemma kpb_flipAll_setClosed_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  kpb_flipAll (StatMech.setClosed e ω) = StatMech.setOpen e (kpb_flipAll ω) := by
-- proof
  apply StatMech.Probability.kpb_flipAll_setClosed e ω

/--
[kpb_infl_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean)
-/
@[path]
private lemma kpb_infl_flip_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {g : ConfigSpace E → ℝ}
  {e : E} :
-- imply
  OSSS.infl (OSSS.bernoulliWeight (1 - p)) g e = OSSS.infl (OSSS.bernoulliWeight p) (fun ω => g (kpb_flipAll ω)) e := by
-- proof
  apply StatMech.Probability.kpb_infl_flip p g e

/--
[kpb_var_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean)
-/
@[path]
private lemma kpb_var_flip_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {g : ConfigSpace E → ℝ} :
-- imply
  OSSS.var (OSSS.bernoulliWeight (1 - p)) g = OSSS.var (OSSS.bernoulliWeight p) (fun ω => g (kpb_flipAll ω)) := by
-- proof
  apply StatMech.Probability.kpb_var_flip p g

/--
[kpb_totalInfl_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean)
-/
@[path]
private lemma kpb_totalInfl_flip_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {g : ConfigSpace E → ℝ} :
-- imply
  totalInfl (OSSS.bernoulliWeight (1 - p)) g = totalInfl (OSSS.bernoulliWeight p) (fun ω => g (kpb_flipAll ω)) := by
-- proof
  apply StatMech.Probability.kpb_totalInfl_flip p g

/--
[kpb_maxInfl_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean)
-/
@[path]
private lemma kpb_maxInfl_flip_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {p : ℝ}
  {g : ConfigSpace E → ℝ} :
-- imply
  maxInfl (OSSS.bernoulliWeight (1 - p)) g = maxInfl (OSSS.bernoulliWeight p) (fun ω => g (kpb_flipAll ω)) := by
-- proof
  apply StatMech.Probability.kpb_maxInfl_flip p g

/--
[kpb_kkl_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean)
-/
@[path]
private lemma kpb_kkl_reflect_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {H : KKLHypercontractive p 2} :
-- imply
  KKLHypercontractive (1 - p) 2 := by
-- proof
  apply StatMech.Probability.kpb_kkl_reflect H

/--
[kpb_residue_c0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean)
-/
@[path]
private lemma kpb_residue_c0_eq
  [Fintype E]
  [DecidableEq E]
  {q : ℝ}
-- given
  (hq : q ≤ 1) :
-- imply
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, KKLHypercontractive p 0 := by
-- proof
  apply StatMech.Probability.kpb_residue_c0 hq

/--
[kpb_PBiasedHC_half_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean)
-/
@[path]
private lemma kpb_PBiasedHC_half_holds_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  KKLHypercontractive (1 / 2 : ℝ) 2 := by
-- proof
  apply StatMech.Probability.kpb_PBiasedHC_half_holds

/--
[kpb_residue_noncirc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean)
-/
@[path]
private lemma kpb_residue_noncirc_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {H : KKLHypercontractive p 2}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool} :
-- imply
  2 * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.kpb_residue_noncirc H φ

/--
[kpb_kkl_pbiased](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean)
-/
@[path]
private lemma kpb_kkl_pbiased_eq
  [Fintype E]
  [DecidableEq E]
  {q : ℝ}
  {Hpb : kpb_PBiasedHC q} :
-- imply
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, KKLHypercontractive p 2 := by
-- proof
  apply StatMech.Probability.kpb_kkl_pbiased Hpb

/--
[kpb_Hbkkkl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean)
-/
@[path]
private lemma kpb_Hbkkkl_eq
  [Fintype E]
  [DecidableEq E]
  {q : ℝ}
  {Hpb : kpb_PBiasedHC q} :
-- imply
  ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), KKLHypercontractive p 2 := by
-- proof
  apply StatMech.Probability.kpb_Hbkkkl Hpb

/--
[kpb_sharpThreshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean)
-/
@[path]
private lemma kpb_sharpThreshold_eq
  [Fintype E]
  [DecidableEq E]
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {A : Set (ConfigSpace E)}
  [DecidablePred (· ∈ A)]
  {q v₀ L : ℝ}
  {Hpb : kpb_PBiasedHC q}
-- given
  (hA : IsIncreasing A)
  (hq : (1 : ℝ) / 2 ≤ q)
  (hv0 : 0 ≤ v₀)
  (hL : 0 ≤ L)
  (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
  (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
  (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), L ≤ StatMech.TwoDim.kklw_logMaxInfl p A) :
-- imply
  1 / 2 + (2 * v₀ * L) * (q - 1 / 2) ≤ StatMech.prob q A := by
-- proof
  apply StatMech.Probability.kpb_sharpThreshold A hA hq hv0 hL hhalf Hpb hvar hLL'

/--
[kpb_sharpThreshold_window](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLpBiased.lean)
-/
@[path]
private lemma kpb_sharpThreshold_window_eq
  [Fintype E]
  [DecidableEq E]
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {A : Set (ConfigSpace E)}
  [DecidablePred (· ∈ A)]
  {q v₀ L ε : ℝ}
  {Hpb : kpb_PBiasedHC q}
-- given
  (hA : IsIncreasing A)
  (hq : (1 : ℝ) / 2 ≤ q)
  (hM : 0 < 2 * v₀ * L)
  (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
  (hv0 : 0 ≤ v₀)
  (hL : 0 ≤ L)
  (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
  (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), L ≤ StatMech.TwoDim.kklw_logMaxInfl p A)
  (hnotyet : StatMech.prob q A ≤ 1 - ε) :
-- imply
  q - 1 / 2 ≤ (1 / 2 - ε) / (2 * v₀ * L) := by
-- proof
  apply StatMech.Probability.kpb_sharpThreshold_window A hA hq hM hhalf hv0 hL Hpb hvar hLL' hnotyet


-- created on 2026-10-23
