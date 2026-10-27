import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.FSRhoOptimise
open Finset Real StatMech StatMech.Probability


/--
[fsr_ptn_psi_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSRhoOptimise.lean)
-/
@[path]
private lemma fsr_ptn_psi_half_eq
  [Fintype ι]
  [DecidableEq ι]
  {b : Bool} :
-- imply
  ptn_psi (1 / 2 : ℝ) b = - khc_sign b := by
-- proof
  apply StatMech.Probability.fsr_ptn_psi_half b

/--
[fsr_ptn_pchar_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSRhoOptimise.lean)
-/
@[path]
private lemma fsr_ptn_pchar_half_eq
  [Fintype ι]
  [DecidableEq ι]
  {S : Finset ι}
  {ω : ConfigSpace ι} :
-- imply
  ptn_pchar (1 / 2 : ℝ) S ω = (-1) ^ S.card * khc_walshChar S ω := by
-- proof
  apply StatMech.Probability.fsr_ptn_pchar_half S ω

/--
[fsr_ptn_coeff_half_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSRhoOptimise.lean)
-/
@[path]
private lemma fsr_ptn_coeff_half_sq_eq
  [Fintype ι]
  [DecidableEq ι]
  {f : ConfigSpace ι → ℝ}
  {S : Finset ι} :
-- imply
  (ptn_coeff (1 / 2 : ℝ) f S) ^ 2 = (khc_fourierCoeff f S) ^ 2 := by
-- proof
  apply StatMech.Probability.fsr_ptn_coeff_half_sq f S

/--
[fsr_totalInfl_half_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSRhoOptimise.lean)
-/
@[path]
private lemma fsr_totalInfl_half_eq_eq
  [Fintype ι]
  [DecidableEq ι]
  {φ : ConfigSpace ι → Bool} :
-- imply
  totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) = ∑ S : Finset ι, 4 * (S.card : ℝ) * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
-- proof
  apply StatMech.Probability.fsr_totalInfl_half_eq φ

/--
[fsr_smallDeltaBound_at_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSRhoOptimise.lean)
-/
@[path]
private lemma fsr_smallDeltaBound_at_half_eq
  [Fintype ι]
  [DecidableEq ι]
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
  {u : ℝ}
-- given
  (hu0 : 0 < u)
  (hu1 : u < 1) :
-- imply
  (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.fsr_smallDeltaBound_at_half φ hu0 hu1

/--
[fsr_pbiased_endpoint_proved](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSRhoOptimise.lean)
-/
@[path]
private lemma fsr_pbiased_endpoint_proved_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  KKLHypercontractive (1 / 2 : ℝ) 2 := by
-- proof
  apply StatMech.Probability.fsr_pbiased_endpoint_proved

/--
[fsr_pbiased_engine_is_damped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSRhoOptimise.lean)
-/
@[path]
private lemma fsr_pbiased_engine_is_damped_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hu0 : 0 ≤ u)
  (hu1 : u ≤ 1) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * ((4 * p * (1 - p)) ^ (S.card - 1) / (4 * p * (1 - p))) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.fsr_pbiased_engine_is_damped hp0 hp1 φ hu0 hu1

/--
[fsr_smallDelta_of_pbiased](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FSRhoOptimise.lean)
-/
@[path]
private lemma fsr_smallDelta_of_pbiased_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : dtr_lowDegreeResidue q} :
-- imply
  cvg_smallDeltaResidue q := by
-- proof
  apply StatMech.Probability.fsr_smallDelta_of_pbiased H


-- created on 2026-10-23
