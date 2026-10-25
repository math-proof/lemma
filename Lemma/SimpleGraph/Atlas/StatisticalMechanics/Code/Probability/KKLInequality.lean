import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.KKLInequality.Part4
open Finset StatMech StatMech.Probability


/--
[kkl_infl_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLInequality.lean)
-/
@[path]
private lemma kkl_infl_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {g : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hν : IsProbWeight ν) :
-- imply
  0 ≤ OSSS.infl ν g e := by
-- proof
  apply StatMech.Probability.kkl_infl_nonneg hν g e

/--
[kkl_totalInfl_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLInequality.lean)
-/
@[path]
private lemma kkl_totalInfl_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {g : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  0 ≤ totalInfl ν g := by
-- proof
  apply StatMech.Probability.kkl_totalInfl_nonneg hν g

/--
[kkl_infl_le_maxInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLInequality.lean)
-/
@[path]
private lemma kkl_infl_le_maxInfl_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {ν : E → Bool → ℝ}
  {g : ConfigSpace E → ℝ}
  {e : E} :
-- imply
  OSSS.infl ν g e ≤ maxInfl ν g := by
-- proof
  apply StatMech.Probability.kkl_infl_le_maxInfl ν g e

/--
[kkl_exists_maxInfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLInequality.lean)
-/
@[path]
private lemma kkl_exists_maxInfl_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {ν : E → Bool → ℝ}
  {g : ConfigSpace E → ℝ} :
-- imply
  ∃ e, OSSS.infl ν g e = maxInfl ν g := by
-- proof
  apply StatMech.Probability.kkl_exists_maxInfl ν g

/--
[kkl_maxInfl_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLInequality.lean)
-/
@[path]
private lemma kkl_maxInfl_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {ν : E → Bool → ℝ}
  {g : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  0 ≤ maxInfl ν g := by
-- proof
  apply StatMech.Probability.kkl_maxInfl_nonneg hν g

/--
[kkl_maxInfl_ge_avg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLInequality.lean)
-/
@[path]
private lemma kkl_maxInfl_ge_avg_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {ν : E → Bool → ℝ}
  {g : ConfigSpace E → ℝ} :
-- imply
  totalInfl ν g ≤ (Fintype.card E : ℝ) * maxInfl ν g := by
-- proof
  apply StatMech.Probability.kkl_maxInfl_ge_avg ν g

/--
[kkl_var_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLInequality.lean)
-/
@[path]
private lemma kkl_var_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {g : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  0 ≤ OSSS.var ν g := by
-- proof
  apply StatMech.Probability.kkl_var_nonneg hν g

/--
[kkl_var_indicator_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLInequality.lean)
-/
@[path]
private lemma kkl_var_indicator_eq_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {φ : ConfigSpace E → Bool} :
-- imply
  OSSS.var ν (fun ω => if φ ω then (1 : ℝ) else 0) = OSSS.expect ν (fun ω => if φ ω then (1 : ℝ) else 0) * (1 - OSSS.expect ν (fun ω => if φ ω then (1 : ℝ) else 0)) := by
-- proof
  apply StatMech.Probability.kkl_var_indicator_eq ν φ

/--
[kkl_var_le_quarter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLInequality.lean)
-/
@[path]
private lemma kkl_var_le_quarter_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {φ : ConfigSpace E → Bool} :
-- imply
  OSSS.var ν (fun ω => if φ ω then (1 : ℝ) else 0) ≤ 1 / 4 := by
-- proof
  apply StatMech.Probability.kkl_var_le_quarter ν φ

/--
[kkl_var_le_total_influence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLInequality.lean)
-/
@[path]
private lemma kkl_var_le_total_influence_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {φ : ConfigSpace E → Bool}
-- given
  (hν : IsProbWeight ν) :
-- imply
  OSSS.var ν (fun ω => if φ ω then (1 : ℝ) else 0) ≤ totalInfl ν (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.kkl_var_le_total_influence hν φ

/--
[kkl_inequality_total](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLInequality.lean)
-/
@[path]
private lemma kkl_inequality_total_eq
  [Fintype E]
  [DecidableEq E]
  {p c : ℝ}
  {H : KKLHypercontractive p c}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool} :
-- imply
  c * OSSS.var (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * Real.log (1 / maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ totalInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.kkl_inequality_total H φ

/--
[kkl_inequality_max](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLInequality.lean)
-/
@[path]
private lemma kkl_inequality_max_eq
  [Fintype E]
  [DecidableEq E]
  {p c : ℝ}
  {H : KKLHypercontractive p c}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool} :
-- imply
  c * OSSS.var (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * Real.log (1 / maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ (Fintype.card E : ℝ) * maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.kkl_inequality_max H φ

/--
[kkl_hypercontractive_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLInequality.lean)
-/
@[path]
private lemma kkl_hypercontractive_zero_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  KKLHypercontractive p 0 := by
-- proof
  apply StatMech.Probability.kkl_hypercontractive_zero p hp0 hp1

/--
[kkl_inequality_total_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLInequality.lean)
-/
@[path]
private lemma kkl_inequality_total_bernoulli_eq
  [Fintype E]
  [DecidableEq E]
  {p c : ℝ}
  {H : KKLHypercontractive p c}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool} :
-- imply
  c * OSSS.var (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * Real.log (1 / maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ totalInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.kkl_inequality_total_bernoulli H φ

/--
[kkl_inequality_max_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLInequality.lean)
-/
@[path]
private lemma kkl_inequality_max_bernoulli_eq
  [Fintype E]
  [DecidableEq E]
  {p c : ℝ}
  {H : KKLHypercontractive p c}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool} :
-- imply
  c * OSSS.var (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) * Real.log (1 / maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ (Fintype.card E : ℝ) * maxInfl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.kkl_inequality_max_bernoulli H φ


-- created on 2026-10-23
