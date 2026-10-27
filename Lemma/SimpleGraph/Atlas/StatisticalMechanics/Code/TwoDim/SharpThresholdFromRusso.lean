import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.TwoDim.SharpThresholdFromRusso
open MeasureTheory Set Filter Topology StatMech StatMech.TwoDim


/--
[sth_prob_differentiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SharpThresholdFromRusso.lean)
-/
@[path]
private lemma sth_prob_differentiable_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)} :
-- imply
  Differentiable ℝ (fun p => prob p A) := by
-- proof
  apply StatMech.TwoDim.sth_prob_differentiable A

/--
[sth_sum_configWeight_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SharpThresholdFromRusso.lean)
-/
@[path]
private lemma sth_sum_configWeight_eq_one_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ} :
-- imply
  ∑ ω : ConfigSpace E, configWeight p ω = 1 := by
-- proof
  apply StatMech.TwoDim.sth_sum_configWeight_eq_one p

/--
[sth_prob_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SharpThresholdFromRusso.lean)
-/
@[path]
private lemma sth_prob_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  prob p A ≤ 1 := by
-- proof
  apply StatMech.TwoDim.sth_prob_le_one A hp0 hp1

/--
[sth_prob_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SharpThresholdFromRusso.lean)
-/
@[path]
private lemma sth_prob_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {p : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  0 ≤ prob p A := by
-- proof
  apply StatMech.TwoDim.sth_prob_nonneg A hp0 hp1

/--
[sth_prob_monotoneOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SharpThresholdFromRusso.lean)
-/
@[path]
private lemma sth_prob_monotoneOn_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
-- given
  (hA : IsIncreasing A) :
-- imply
  MonotoneOn (fun p => prob p A) (Set.Icc (0 : ℝ) 1) := by
-- proof
  apply StatMech.TwoDim.sth_prob_monotoneOn A hA

/--
[sth_prob_sub_ge_of_deriv_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SharpThresholdFromRusso.lean)
-/
@[path]
private lemma sth_prob_sub_ge_of_deriv_ge_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {a b M : ℝ}
-- given
  (hab : a ≤ b)
  (hge : ∀ p ∈ interior (Set.Icc a b), M ≤ deriv (fun p => prob p A) p) :
-- imply
  M * (b - a) ≤ prob b A - prob a A := by
-- proof
  apply StatMech.TwoDim.sth_prob_sub_ge_of_deriv_ge A hab hge

/--
[sth_sharpThreshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SharpThresholdFromRusso.lean)
-/
@[path]
private lemma sth_sharpThreshold_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {q M : ℝ}
-- given
  (hA : IsIncreasing A)
  (hq : (1 : ℝ) / 2 ≤ q)
  (hhalf : prob (1 / 2) A = 1 / 2)
  (hinfl : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), M ≤ ∑ e, influence p A e) :
-- imply
  1 / 2 + M * (q - 1 / 2) ≤ prob q A := by
-- proof
  apply StatMech.TwoDim.sth_sharpThreshold A hA hq hhalf hinfl

/--
[sth_sharpThreshold_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SharpThresholdFromRusso.lean)
-/
@[path]
private lemma sth_sharpThreshold_eq_one_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {q M : ℝ}
-- given
  (hA : IsIncreasing A)
  (hq : (1 : ℝ) / 2 ≤ q)
  (hq1 : q ≤ 1)
  (hhalf : prob (1 / 2) A = 1 / 2)
  (hinfl : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), M ≤ ∑ e, influence p A e)
  (hsat : 1 ≤ 1 / 2 + M * (q - 1 / 2)) :
-- imply
  prob q A = 1 := by
-- proof
  apply StatMech.TwoDim.sth_sharpThreshold_eq_one A hA hq hq1 hhalf hinfl hsat

/--
[sth_sharpThreshold_window](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SharpThresholdFromRusso.lean)
-/
@[path]
private lemma sth_sharpThreshold_window_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {q M ε : ℝ}
-- given
  (hA : IsIncreasing A)
  (hM : 0 < M)
  (hq : (1 : ℝ) / 2 ≤ q)
  (hhalf : prob (1 / 2) A = 1 / 2)
  (hinfl : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), M ≤ ∑ e, influence p A e)
  (hnotyet : prob q A ≤ 1 - ε) :
-- imply
  q - 1 / 2 ≤ (1 / 2 - ε) / M := by
-- proof
  apply StatMech.TwoDim.sth_sharpThreshold_window A hA hM hq hhalf hinfl hnotyet

/--
[sth_sharpThreshold_pivotal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SharpThresholdFromRusso.lean)
-/
@[path]
private lemma sth_sharpThreshold_pivotal_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {q M : ℝ}
-- given
  (hA : IsIncreasing A)
  (hq : (1 : ℝ) / 2 ≤ q)
  (hhalf : prob (1 / 2) A = 1 / 2)
  (hpiv : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), M ≤ ∑ e, pivotalProb p A e) :
-- imply
  1 / 2 + M * (q - 1 / 2) ≤ prob q A := by
-- proof
  apply StatMech.TwoDim.sth_sharpThreshold_pivotal A hA hq hhalf hpiv


-- created on 2026-10-23
