import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.NearHalfBKKKL
open Finset StatMech StatMech.Probability


/--
[nhb_var_le_damped_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/NearHalfBKKKL.lean)
-/
@[path]
private lemma nhb_var_le_damped_add_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {p : ℝ}
  {φ : ConfigSpace E → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) ≤ (∑ S ∈ (univ.erase (∅ : Finset E)), ((4 * p * (1 - p)) ^ (S.card - 1) / (4 * p * (1 - p))) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) + (1 - 4 * p * (1 - p)) * (ptn_sigma p) ^ 2 * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.nhb_var_le_damped_add hp0 hp1 φ

/--
[nhb_nearHalf_kkl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/NearHalfBKKKL.lean)
-/
@[path]
private lemma nhb_nearHalf_kkl_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {p : ℝ}
  {φ : ConfigSpace E → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  2 * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ (1 + 2 * (1 - 4 * p * (1 - p)) * (ptn_sigma p) ^ 2 * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.nhb_nearHalf_kkl hp0 hp1 φ

/--
[nhb_nearHalf_kkl_absorbed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/NearHalfBKKKL.lean)
-/
@[path]
private lemma nhb_nearHalf_kkl_absorbed_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {p : ℝ}
  {φ : ConfigSpace E → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hcorr : 2 * (1 - 4 * p * (1 - p)) * (ptn_sigma p) ^ 2 * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ 1) :
-- imply
  OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.nhb_nearHalf_kkl_absorbed hp0 hp1 φ hcorr


-- created on 2026-10-23
