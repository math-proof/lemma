import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.TwoPointLSI
open Real Set StatMech StatMech.Probability


/--
[tpl_ent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointLSI.lean)
-/
@[path]
private lemma tpl_ent_eq_eq
  {p a b : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (ha : 0 < a)
  (hb : 0 < b) :
-- imply
  tpl_ent p a b = (1 - p) * a * Real.log (a / tpl_mean p a b) + p * b * Real.log (b / tpl_mean p a b) := by
-- proof
  apply StatMech.Probability.tpl_ent_eq hp0 hp1 ha hb

/--
[tpl_chiSq_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointLSI.lean)
-/
@[path]
private lemma tpl_chiSq_bound_eq
  {p a b : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (ha : 0 < a)
  (hb : 0 < b) :
-- imply
  tpl_ent p a b ≤ p * (1 - p) * (a - b) ^ 2 / tpl_mean p a b := by
-- proof
  apply StatMech.Probability.tpl_chiSq_bound hp0 hp1 ha hb

/--
[tpl_cauchy_schwarz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointLSI.lean)
-/
@[path]
private lemma tpl_cauchy_schwarz_eq
  {p x y : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  p * (1 - p) * (x + y) ^ 2 ≤ (1 - p) * x ^ 2 + p * y ^ 2 := by
-- proof
  apply StatMech.Probability.tpl_cauchy_schwarz hp0 hp1

/--
[tpl_var_div_mean_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointLSI.lean)
-/
@[path]
private lemma tpl_var_div_mean_le_eq
  {p g0 g1 : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hpos : 0 < g0 ∨ 0 < g1) :
-- imply
  p * (1 - p) * (g0 ^ 2 - g1 ^ 2) ^ 2 / ((1 - p) * g0 ^ 2 + p * g1 ^ 2) ≤ (g0 - g1) ^ 2 := by
-- proof
  apply StatMech.Probability.tpl_var_div_mean_le hp0 hp1 hpos

/--
[tpl_lsi_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointLSI.lean)
-/
@[path]
private lemma tpl_lsi_pos_eq
  {p g0 g1 : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 < g0)
  (h1 : 0 < g1) :
-- imply
  tpl_ent p (g0 ^ 2) (g1 ^ 2) ≤ (g0 - g1) ^ 2 := by
-- proof
  apply StatMech.Probability.tpl_lsi_pos hp0 hp1 h0 h1

/--
[tpl_boundary_scalar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointLSI.lean)
-/
@[path]
private lemma tpl_boundary_scalar_eq
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  -((1 - p) * Real.log (1 - p)) ≤ p := by
-- proof
  apply StatMech.Probability.tpl_boundary_scalar hp0 hp1

/--
[tpl_lsi_b_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointLSI.lean)
-/
@[path]
private lemma tpl_lsi_b_zero_eq
  {p g0 : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ g0) :
-- imply
  tpl_ent p (g0 ^ 2) 0 ≤ (g0 - 0) ^ 2 := by
-- proof
  apply StatMech.Probability.tpl_lsi_b_zero hp0 hp1 h0

/--
[tpl_ent_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointLSI.lean)
-/
@[path]
private lemma tpl_ent_swap_eq
  {p a b : ℝ} :
-- imply
  tpl_ent p a b = tpl_ent (1 - p) b a := by
-- proof
  apply StatMech.Probability.tpl_ent_swap p a b

/--
[tpl_lsi_a_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointLSI.lean)
-/
@[path]
private lemma tpl_lsi_a_zero_eq
  {p g1 : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ g1) :
-- imply
  tpl_ent p 0 (g1 ^ 2) ≤ (0 - g1) ^ 2 := by
-- proof
  apply StatMech.Probability.tpl_lsi_a_zero hp0 hp1 h0

/--
[tpl_lsi_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointLSI.lean)
-/
@[path]
private lemma tpl_lsi_nonneg_eq
  {p g0 g1 : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (h0 : 0 ≤ g0)
  (h1 : 0 ≤ g1) :
-- imply
  tpl_ent p (g0 ^ 2) (g1 ^ 2) ≤ (g0 - g1) ^ 2 := by
-- proof
  apply StatMech.Probability.tpl_lsi_nonneg hp0 hp1 h0 h1

/--
[tpl_lsi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointLSI.lean)
-/
@[path]
private lemma tpl_lsi_eq
  {p : ℝ}
  {g0 g1 : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  tpl_ent p (g0 ^ 2) (g1 ^ 2) ≤ (g0 - g1) ^ 2 := by
-- proof
  apply StatMech.Probability.tpl_lsi hp0 hp1 g0 g1

/--
[tpl_lsi_weighted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointLSI.lean)
-/
@[path]
private lemma tpl_lsi_weighted_eq
  {p : ℝ}
  {g0 g1 : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  tpl_ent p (g0 ^ 2) (g1 ^ 2) ≤ (1 / (p * (1 - p))) * (p * (1 - p) * (g0 - g1) ^ 2) := by
-- proof
  apply StatMech.Probability.tpl_lsi_weighted hp0 hp1 g0 g1

/--
[tpl_ent_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointLSI.lean)
-/
@[path]
private lemma tpl_ent_nonneg_eq
  {p a b : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (ha : 0 ≤ a)
  (hb : 0 ≤ b) :
-- imply
  0 ≤ tpl_ent p a b := by
-- proof
  apply StatMech.Probability.tpl_ent_nonneg hp0 hp1 ha hb

/--
[tpl_chiSq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointLSI.lean)
-/
@[path]
private lemma tpl_chiSq_eq
  {p a b : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (ha : 0 ≤ a)
  (hb : 0 ≤ b)
  (hpos : 0 < a ∨ 0 < b) :
-- imply
  tpl_ent p a b ≤ p * (1 - p) * (a - b) ^ 2 / tpl_mean p a b := by
-- proof
  apply StatMech.Probability.tpl_chiSq hp0 hp1 ha hb hpos


-- created on 2026-10-23
