import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.PBiasedKKLClose
open Finset Real StatMech StatMech.Probability


/--
[pkc_kkl_logGain_largeInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLClose.lean)
-/
@[path]
private lemma pkc_kkl_logGain_largeInfl_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hδlo : Real.exp (-(1 / (2 * (p * (1 - p))))) ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :
-- imply
  2 * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.pkc_kkl_logGain_largeInfl hp0 hp1 φ hδlo

/--
[pkc_kkl_logGain_largeInfl'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLClose.lean)
-/
@[path]
private lemma pkc_kkl_logGain_largeInfl'_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hδlo : Real.exp (-(1 / (2 * (p * (1 - p))))) ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :
-- imply
  2 * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.pkc_kkl_logGain_largeInfl' hp0 hp1 φ hδlo

/--
[pkc_threshold_le_exp_neg_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLClose.lean)
-/
@[path]
private lemma pkc_threshold_le_exp_neg_two_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  Real.exp (-(1 / (2 * (p * (1 - p))))) ≤ Real.exp (-2) := by
-- proof
  apply StatMech.Probability.pkc_threshold_le_exp_neg_two hp0 hp1

/--
[pkc_threshold_antitone_to_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLClose.lean)
-/
@[path]
private lemma pkc_threshold_antitone_to_one_eq
  [Fintype ι]
  [DecidableEq ι]
  {p p' : ℝ}
-- given
  (hp : 1 / 2 ≤ p)
  (hpp' : p < p')
  (hp'1 : p' < 1) :
-- imply
  Real.exp (-(1 / (2 * (p' * (1 - p'))))) ≤ Real.exp (-(1 / (2 * (p * (1 - p))))) := by
-- proof
  apply StatMech.Probability.pkc_threshold_antitone_to_one hp hpp' hp'1

/--
[pkc_dampingWitness_of_hard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLClose.lean)
-/
@[path]
private lemma pkc_dampingWitness_of_hard_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : esa_DampingHard q} :
-- imply
  pen_DampingWitness q := by
-- proof
  apply StatMech.Probability.pkc_dampingWitness_of_hard H

/--
[pkc_rhoOptimise_of_hard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLClose.lean)
-/
@[path]
private lemma pkc_rhoOptimise_of_hard_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : esa_DampingHard q} :
-- imply
  ptn_RhoOptimise q := by
-- proof
  apply StatMech.Probability.pkc_rhoOptimise_of_hard H

/--
[pkc_PBiasedHC_of_hard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLClose.lean)
-/
@[path]
private lemma pkc_PBiasedHC_of_hard_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : esa_DampingHard q}
-- given
  (hq : q ≤ 1) :
-- imply
  kpb_PBiasedHC q := by
-- proof
  apply StatMech.Probability.pkc_PBiasedHC_of_hard hq H

/--
[pkc_kklHC_of_hard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLClose.lean)
-/
@[path]
private lemma pkc_kklHC_of_hard_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : esa_DampingHard q}
  {p : ℝ}
-- given
  (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q)
  (hp1 : p < 1) :
-- imply
  KKLHypercontractive p 2 := by
-- proof
  apply StatMech.Probability.pkc_kklHC_of_hard H hp hp1

/--
[pkc_sharpThreshold_of_hard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedKKLClose.lean)
-/
@[path]
private lemma pkc_sharpThreshold_of_hard_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : esa_DampingHard q}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {A : Set (ConfigSpace E)}
  [DecidablePred (· ∈ A)]
  {v₀ L : ℝ}
-- given
  (hq1 : q ≤ 1)
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
  apply StatMech.Probability.pkc_sharpThreshold_of_hard hq1 H A hA hq hv0 hL hhalf hvar hLL'


-- created on 2026-10-23
