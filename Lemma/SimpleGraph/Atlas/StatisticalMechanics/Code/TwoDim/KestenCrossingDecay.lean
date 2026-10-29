import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.TwoDim.KestenCrossingDecay
open MeasureTheory Set Filter Topology StatMech StatMech.TwoDim


/--
[kcd_localOneArm_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenCrossingDecay.lean)
-/
@[path]
private lemma kcd_localOneArm_prob_eq
  {x : Site 2}
  {n : ℕ}
-- given
  (p : NNReal)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (kcd_localOneArm x n) = crossProb 2 p hp n := by
-- proof
  apply StatMech.TwoDim.kcd_localOneArm_prob p hp x n

/--
[kcd_horizontal_subset_localOneArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenCrossingDecay.lean)
-/
@[path]
private lemma kcd_horizontal_subset_localOneArm_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  StatMech.RSW.Box.horizontalCrossingEvent 0 (n : ℤ) 0 (n : ℤ) ⊆ ⋃ x ∈ boxSV_boxF 2 n, kcd_localOneArm x n := by
-- proof
  apply StatMech.TwoDim.kcd_horizontal_subset_localOneArm n hn

/--
[kcd_horizontal_prob_le_box_mul_crossProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenCrossingDecay.lean)
-/
@[path]
private lemma kcd_horizontal_prob_le_box_mul_crossProb_eq
  {n : ℕ}
-- given
  (p : NNReal)
  (hp : p ≤ 1)
  (hn : 0 < n) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (StatMech.RSW.Box.horizontalCrossingEvent 0 (n : ℤ) 0 (n : ℤ)) ≤ ((boxSV_boxF 2 n).card : ℝ) * crossProb 2 p hp n := by
-- proof
  apply StatMech.TwoDim.kcd_horizontal_prob_le_box_mul_crossProb p hp n hn

/--
[kcd_quadratic_mul_exp_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenCrossingDecay.lean)
-/
@[path]
private lemma kcd_quadratic_mul_exp_tendsto_zero_eq
  {c C : ℝ}
-- given
  (hc : 0 < c) :
-- imply
  Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) ^ 2 * (C * Real.exp (-c * n))) atTop (𝓝 0) := by
-- proof
  apply StatMech.TwoDim.kcd_quadratic_mul_exp_tendsto_zero hc

/--
[kcd_horizontal_tendsto_zero_of_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenCrossingDecay.lean)
-/
@[path]
private lemma kcd_horizontal_tendsto_zero_of_exp_eq
-- given
  (p : NNReal)
  (hp : p ≤ 1)
  (hdecay : ∃ c > 0, ∃ C > 0, ∀ n, 0 < n → crossProb 2 p hp n ≤ C * Real.exp (-c * n)) :
-- imply
  Tendsto (fun n : ℕ => (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (StatMech.RSW.Box.horizontalCrossingEvent 0 (n : ℤ) 0 (n : ℤ))) atTop (𝓝 0) := by
-- proof
  apply StatMech.TwoDim.kcd_horizontal_tendsto_zero_of_exp p hp hdecay

/--
[kcd_crossProb_mono_param](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenCrossingDecay.lean)
-/
@[path]
private lemma kcd_crossProb_mono_param_eq
  {p q : NNReal}
  {n : ℕ}
-- given
  (hp : p ≤ 1)
  (hq : q ≤ 1)
  (hpq : p ≤ q)
  (hn : 0 < n) :
-- imply
  crossProb 2 p hp n ≤ crossProb 2 q hq n := by
-- proof
  apply StatMech.TwoDim.kcd_crossProb_mono_param hp hq hpq hn

/--
[kcd_horizontal_sharpThreshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenCrossingDecay.lean)
-/
@[path]
private lemma kcd_horizontal_sharpThreshold_eq :
-- imply
  ∀ (p : NNReal) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 → Tendsto (fun n : ℕ => (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (StatMech.RSW.Box.horizontalCrossingEvent 0 (n : ℤ) 0 (n : ℤ))) atTop (𝓝 0) := by
-- proof
  apply StatMech.TwoDim.kcd_horizontal_sharpThreshold


-- created on 2026-10-23
