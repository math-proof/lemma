import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.Sharpness.Part2
open MeasureTheory Set Filter StatMech StatMech.Percolation


/--
[gronwall_dct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Sharpness.lean)
-/
@[path]
private lemma gronwall_dct_eq
  {d : ℕ}
  {f f' : ℝ → ℝ}
  {a p : ℝ}
-- given
  (ha0 : 0 < a)
  (hap : a < p)
  (hp1 : p < 1)
  (hcont : ContinuousOn f (Icc a p))
  (hub : ∀ t ∈ Icc a p, f t ≤ 1)
  (hfa : 0 ≤ f a)
  (hderiv : ∀ t ∈ Ioo a p, HasDerivAt f (f' t) t)
  (hdiff_ineq : ∀ t ∈ Ioo a p, f' t ≥ (1 / (t * (1 - t))) * (1 - f t)) :
-- imply
  f p ≥ (p - a) / (p * (1 - a)) := by
-- proof
  apply StatMech.Percolation.gronwall_dct f f' a p ha0 hap hp1 hcont hub hfa hderiv hdiff_ineq

/--
[crossProbReal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Sharpness.lean)
-/
@[path]
private lemma crossProbReal_eq_eq
  {d : ℕ}
  {d n : ℕ}
-- given
  (p : NNReal)
  (hp : p ≤ 1) :
-- imply
  crossProbReal d n (p : ℝ) = crossProb d p hp n := by
-- proof
  apply StatMech.Percolation.crossProbReal_eq d n p hp

/--
[crossProbReal_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Sharpness.lean)
-/
@[path]
private lemma crossProbReal_le_one_eq
  {d : ℕ}
  {d n : ℕ}
  {t : ℝ} :
-- imply
  crossProbReal d n t ≤ 1 := by
-- proof
  apply StatMech.Percolation.crossProbReal_le_one d n t

/--
[crossProbReal_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Sharpness.lean)
-/
@[path]
private lemma crossProbReal_nonneg_eq
  {d : ℕ}
  {d n : ℕ}
  {t : ℝ} :
-- imply
  0 ≤ crossProbReal d n t := by
-- proof
  apply StatMech.Percolation.crossProbReal_nonneg d n t

/--
[measurableSet_crossingEvent'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Sharpness.lean)
-/
@[path]
private lemma measurableSet_crossingEvent'_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  MeasurableSet (crossingEvent d n) := by
-- proof
  apply StatMech.Percolation.measurableSet_crossingEvent' n

/--
[percolationEvent_eq_iInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Sharpness.lean)
-/
@[path]
private lemma percolationEvent_eq_iInter_eq
  {d : ℕ} :
-- imply
  percolationEvent d = ⋂ n : ℕ, crossingEvent d (n + 1) := by
-- proof
  apply StatMech.Percolation.percolationEvent_eq_iInter

/--
[tendsto_crossProb_theta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Sharpness.lean)
-/
@[path]
private lemma tendsto_crossProb_theta_eq
  {d : ℕ}
-- given
  (p : NNReal)
  (hp : p ≤ 1) :
-- imply
  Tendsto (fun n => crossProb d p hp (n + 1)) atTop (𝓝 (theta d p hp)) := by
-- proof
  apply StatMech.Percolation.tendsto_crossProb_theta p hp

/--
[theta_eq_zero_of_crossProb_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Sharpness.lean)
-/
@[path]
private lemma theta_eq_zero_of_crossProb_decay_eq
  {d : ℕ}
-- given
  (p : NNReal)
  (hp : p ≤ 1)
  (hdecay : ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n)) :
-- imply
  theta d p hp = 0 := by
-- proof
  apply StatMech.Percolation.theta_eq_zero_of_crossProb_decay p hp hdecay

/--
[theta_ge_meanField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Sharpness.lean)
-/
@[path]
private lemma theta_ge_meanField_eq
  {d : ℕ}
  {a : ℝ}
  {F' : ℕ → ℝ → ℝ}
-- given
  (q : NNReal)
  (hq : q ≤ 1)
  (ha0 : 0 < a)
  (haq : a < (q : ℝ))
  (hq1 : (q : ℝ) < 1)
  (hcont : ∀ n, ContinuousOn (crossProbReal d (n + 1)) (Icc a (q : ℝ)))
  (hderiv : ∀ n, ∀ t ∈ Ioo a (q : ℝ), HasDerivAt (crossProbReal d (n + 1)) (F' n t) t)
  (hdiffineq : ∀ n, ∀ t ∈ Ioo a (q : ℝ), F' n t ≥ (1 / (t * (1 - t))) * (1 - crossProbReal d (n + 1) t)) :
-- imply
  theta d q hq ≥ ((q : ℝ) - a) / ((q : ℝ) * (1 - a)) := by
-- proof
  apply StatMech.Percolation.theta_ge_meanField q hq a ha0 haq hq1 F' hcont hderiv hdiffineq

/--
[theta_pos_of_meanField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Sharpness.lean)
-/
@[path]
private lemma theta_pos_of_meanField_eq
  {d : ℕ}
  {a : ℝ}
  {F' : ℕ → ℝ → ℝ}
-- given
  (q : NNReal)
  (hq : q ≤ 1)
  (ha0 : 0 < a)
  (haq : a < (q : ℝ))
  (hq1 : (q : ℝ) < 1)
  (hcont : ∀ n, ContinuousOn (crossProbReal d (n + 1)) (Icc a (q : ℝ)))
  (hderiv : ∀ n, ∀ t ∈ Ioo a (q : ℝ), HasDerivAt (crossProbReal d (n + 1)) (F' n t) t)
  (hdiffineq : ∀ n, ∀ t ∈ Ioo a (q : ℝ), F' n t ≥ (1 / (t * (1 - t))) * (1 - crossProbReal d (n + 1) t)) :
-- imply
  0 < theta d q hq := by
-- proof
  apply StatMech.Percolation.theta_pos_of_meanField q hq a ha0 haq hq1 F' hcont hderiv hdiffineq

/--
[tildePc_le_pc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Sharpness.lean)
-/
@[path]
private lemma tildePc_le_pc_eq
  {d : ℕ}
-- given
  (hsub : ∀ p ∈ tildePcSet d, ∀ hp : p ≤ 1, ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n)) :
-- imply
  tildePc d ≤ pc d := by
-- proof
  apply StatMech.Percolation.tildePc_le_pc hsub

/--
[pc_le_tildePc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Sharpness.lean)
-/
@[path]
private lemma pc_le_tildePc_eq
  {d : ℕ}
-- given
  (htheta_one : ∀ h1 : (1 : NNReal) ≤ 1, theta d 1 h1 ≠ 0)
  (hmf : ∀ q : NNReal, ∀ hq : q ≤ 1, tildePc d < q → (q : ℝ) < 1 → 0 < theta d q hq) :
-- imply
  pc d ≤ tildePc d := by
-- proof
  apply StatMech.Percolation.pc_le_tildePc htheta_one hmf

/--
[tildePc_eq_pc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Sharpness.lean)
-/
@[path]
private lemma tildePc_eq_pc_eq
  {d : ℕ}
-- given
  (htheta_one : ∀ h1 : (1 : NNReal) ≤ 1, theta d 1 h1 ≠ 0)
  (hsub : ∀ p ∈ tildePcSet d, ∀ hp : p ≤ 1, ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n))
  (hmf : ∀ q : NNReal, ∀ hq : q ≤ 1, tildePc d < q → (q : ℝ) < 1 → 0 < theta d q hq) :
-- imply
  tildePc d = pc d := by
-- proof
  apply StatMech.Percolation.tildePc_eq_pc htheta_one hsub hmf

/--
[sharpness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Sharpness.lean)
-/
@[path]
private lemma sharpness_eq
  {d : ℕ}
-- given
  (htildePc_pos : 0 < (tildePc d : ℝ))
  (htheta_one : ∀ h1 : (1 : NNReal) ≤ 1, theta d 1 h1 ≠ 0)
  (hsub : ∀ p ∈ tildePcSet d, ∀ hp : p ≤ 1, ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n))
  (F' : ℕ → NNReal → ℝ → ℝ)
  (hcont : ∀ q : NNReal, tildePc d < q → (q : ℝ) < 1 → ∀ n, ContinuousOn (crossProbReal d (n + 1)) (Icc (tildePc d : ℝ) (q : ℝ)))
  (hderiv : ∀ q : NNReal, tildePc d < q → (q : ℝ) < 1 → ∀ n, ∀ t ∈ Ioo (tildePc d : ℝ) (q : ℝ), HasDerivAt (crossProbReal d (n + 1)) (F' n q t) t)
  (hdiffineq : ∀ q : NNReal, tildePc d < q → (q : ℝ) < 1 → ∀ n, ∀ t ∈ Ioo (tildePc d : ℝ) (q : ℝ), F' n q t ≥ (1 / (t * (1 - t))) * (1 - crossProbReal d (n + 1) t)) :
-- imply
  tildePc d = pc d ∧ (∀ p ∈ tildePcSet d, ∀ hp : p ≤ 1, ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n)) ∧ (∀ q : NNReal, ∀ hq : q ≤ 1, tildePc d < q → (q : ℝ) < 1 → theta d q hq ≥ ((q : ℝ) - (tildePc d : ℝ)) / ((q : ℝ) * (1 - (tildePc d : ℝ)))) := by
-- proof
  apply StatMech.Percolation.sharpness htildePc_pos htheta_one hsub F' hcont hderiv hdiffineq


-- created on 2026-10-23
