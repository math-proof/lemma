import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
open StatMech StatMech.Exact3D


/--
[finiteDistanceDecayRate_eq_of_abs_eq_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentialDecayCriteria.lean)
-/
@[path]
private lemma finiteDistanceDecayRate_eq_of_abs_eq_exp_eq
  {G : ℕ → ℝ}
  {A m : ℝ}
  {n : ℕ}
-- given
  (hA : 0 < A)
  (hn : n ≠ 0)
  (hG : |G n| = A * Real.exp (-(m * (n : ℝ)))) :
-- imply
  finiteDistanceDecayRate G n = m - Real.log A / (n : ℝ) := by
-- proof
  apply StatMech.Exact3D.finiteDistanceDecayRate_eq_of_abs_eq_exp G hA hn hG

/--
[finiteDistanceDecayRate_eq_of_abs_eq_prefactor_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentialDecayCriteria.lean)
-/
@[path]
private lemma finiteDistanceDecayRate_eq_of_abs_eq_prefactor_exp_eq
  {G : ℕ → ℝ}
  {A : ℕ → ℝ}
  {m : ℝ}
  {n : ℕ}
-- given
  (hn : n ≠ 0)
  (hA : 0 < A n)
  (hG : |G n| = A n * Real.exp (-(m * (n : ℝ)))) :
-- imply
  finiteDistanceDecayRate G n = m - Real.log (A n) / (n : ℝ) := by
-- proof
  apply StatMech.Exact3D.finiteDistanceDecayRate_eq_of_abs_eq_prefactor_exp G hn hA hG

/--
[tendsto_log_prefactor_div_nat_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentialDecayCriteria.lean)
-/
@[path]
private lemma tendsto_log_prefactor_div_nat_atTop_eq
  {A : ℝ} :
-- imply
  Filter.Tendsto (fun n : ℕ => Real.log A / (n : ℝ)) Filter.atTop (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_log_prefactor_div_nat_atTop A

/--
[finiteDistanceDecayRate_bounds_of_abs_between_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentialDecayCriteria.lean)
-/
@[path]
private lemma finiteDistanceDecayRate_bounds_of_abs_between_exp_eq
  {G : ℕ → ℝ}
  {Alo Ahi m : ℝ}
  {n : ℕ}
-- given
  (hn : n ≠ 0)
  (hlo_pos : 0 < Alo)
  (hhi_pos : 0 < Ahi)
  (hlo : Alo * Real.exp (-(m * (n : ℝ))) ≤ |G n|)
  (hhi : |G n| ≤ Ahi * Real.exp (-(m * (n : ℝ)))) :
-- imply
  m - Real.log Ahi / (n : ℝ) ≤ finiteDistanceDecayRate G n ∧ finiteDistanceDecayRate G n ≤ m - Real.log Alo / (n : ℝ) := by
-- proof
  apply StatMech.Exact3D.finiteDistanceDecayRate_bounds_of_abs_between_exp G hn hlo_pos hhi_pos hlo hhi

/--
[tendsto_finiteDistanceDecayRate_of_eventually_abs_between_prefactor_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentialDecayCriteria.lean)
-/
@[path]
private lemma tendsto_finiteDistanceDecayRate_of_eventually_abs_between_prefactor_exp_eq
  {G : ℕ → ℝ}
  {Alo Ahi : ℕ → ℝ}
  {m : ℝ}
-- given
  (hlo_pos : ∀ᶠ n in Filter.atTop, 0 < Alo n)
  (hhi_pos : ∀ᶠ n in Filter.atTop, 0 < Ahi n)
  (hlog_lo : Filter.Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ)) Filter.atTop (nhds 0))
  (hlog_hi : Filter.Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) Filter.atTop (nhds 0))
  (hlo : ∀ᶠ n in Filter.atTop, Alo n * Real.exp (-(m * (n : ℝ))) ≤ |G n|)
  (hhi : ∀ᶠ n in Filter.atTop, |G n| ≤ Ahi n * Real.exp (-(m * (n : ℝ)))) :
-- imply
  Filter.Tendsto (fun n : ℕ => finiteDistanceDecayRate G n) Filter.atTop (nhds m) := by
-- proof
  apply StatMech.Exact3D.tendsto_finiteDistanceDecayRate_of_eventually_abs_between_prefactor_exp G hlo_pos hhi_pos hlog_lo hlog_hi hlo hhi

/--
[tendsto_neg_log_div_of_eventually_between_prefactor_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentialDecayCriteria.lean)
-/
@[path]
private lemma tendsto_neg_log_div_of_eventually_between_prefactor_exp_eq
  {G : ℕ → ℝ}
  {Alo Ahi : ℕ → ℝ}
  {m : ℝ}
-- given
  (hlo_pos : ∀ᶠ n in Filter.atTop, 0 < Alo n)
  (hhi_pos : ∀ᶠ n in Filter.atTop, 0 < Ahi n)
  (hlog_lo : Filter.Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ)) Filter.atTop (nhds 0))
  (hlog_hi : Filter.Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) Filter.atTop (nhds 0))
  (hlo : ∀ᶠ n in Filter.atTop, Alo n * Real.exp (-(m * (n : ℝ))) ≤ G n)
  (hhi : ∀ᶠ n in Filter.atTop, G n ≤ Ahi n * Real.exp (-(m * (n : ℝ)))) :
-- imply
  Filter.Tendsto (fun n : ℕ => -Real.log (G n) / (n : ℝ)) Filter.atTop (nhds m) := by
-- proof
  apply StatMech.Exact3D.tendsto_neg_log_div_of_eventually_between_prefactor_exp G hlo_pos hhi_pos hlog_lo hlog_hi hlo hhi

/--
[hasInverseCorrelationLength_of_eventually_abs_eq_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentialDecayCriteria.lean)
-/
@[path]
private lemma hasInverseCorrelationLength_of_eventually_abs_eq_exp_eq
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {A m : ℝ}
-- given
  (hA : 0 < A)
  (hG : ∀ᶠ n in Filter.atTop, |TwoPointAlongRay M β origin ray n| = A * Real.exp (-(m * (n : ℝ)))) :
-- imply
  HasInverseCorrelationLength M β origin ray m := by
-- proof
  apply StatMech.Exact3D.hasInverseCorrelationLength_of_eventually_abs_eq_exp M β origin ray hA hG

/--
[hasInverseCorrelationLength_of_eventually_abs_eq_prefactor_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentialDecayCriteria.lean)
-/
@[path]
private lemma hasInverseCorrelationLength_of_eventually_abs_eq_prefactor_exp_eq
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {A : ℕ → ℝ}
  {m : ℝ}
-- given
  (hA : ∀ᶠ n in Filter.atTop, 0 < A n)
  (hlogA : Filter.Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ)) Filter.atTop (nhds 0))
  (hG : ∀ᶠ n in Filter.atTop, |TwoPointAlongRay M β origin ray n| = A n * Real.exp (-(m * (n : ℝ)))) :
-- imply
  HasInverseCorrelationLength M β origin ray m := by
-- proof
  apply StatMech.Exact3D.hasInverseCorrelationLength_of_eventually_abs_eq_prefactor_exp M β origin ray hA hlogA hG

/--
[hasInverseCorrelationLength_of_eventually_abs_between_prefactor_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentialDecayCriteria.lean)
-/
@[path]
private lemma hasInverseCorrelationLength_of_eventually_abs_between_prefactor_exp_eq
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {Alo Ahi : ℕ → ℝ}
  {m : ℝ}
-- given
  (hlo_pos : ∀ᶠ n in Filter.atTop, 0 < Alo n)
  (hhi_pos : ∀ᶠ n in Filter.atTop, 0 < Ahi n)
  (hlog_lo : Filter.Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ)) Filter.atTop (nhds 0))
  (hlog_hi : Filter.Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) Filter.atTop (nhds 0))
  (hlo : ∀ᶠ n in Filter.atTop, Alo n * Real.exp (-(m * (n : ℝ))) ≤ |TwoPointAlongRay M β origin ray n|)
  (hhi : ∀ᶠ n in Filter.atTop, |TwoPointAlongRay M β origin ray n| ≤ Ahi n * Real.exp (-(m * (n : ℝ)))) :
-- imply
  HasInverseCorrelationLength M β origin ray m := by
-- proof
  apply StatMech.Exact3D.hasInverseCorrelationLength_of_eventually_abs_between_prefactor_exp M β origin ray hlo_pos hhi_pos hlog_lo hlog_hi hlo hhi

/--
[hasCorrelationLength_of_eventually_abs_eq_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentialDecayCriteria.lean)
-/
@[path]
private lemma hasCorrelationLength_of_eventually_abs_eq_exp_eq
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {A m : ℝ}
-- given
  (hA : 0 < A)
  (hm : 0 < m)
  (hG : ∀ᶠ n in Filter.atTop, |TwoPointAlongRay M β origin ray n| = A * Real.exp (-(m * (n : ℝ)))) :
-- imply
  HasCorrelationLength M β origin ray m⁻¹ where xi_pos := by
-- proof
  apply StatMech.Exact3D.hasCorrelationLength_of_eventually_abs_eq_exp M β origin ray hA hm hG

/--
[hasCorrelationLength_of_eventually_abs_eq_prefactor_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentialDecayCriteria.lean)
-/
@[path]
private lemma hasCorrelationLength_of_eventually_abs_eq_prefactor_exp_eq
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {A : ℕ → ℝ}
  {m : ℝ}
-- given
  (hA : ∀ᶠ n in Filter.atTop, 0 < A n)
  (hlogA : Filter.Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ)) Filter.atTop (nhds 0))
  (hm : 0 < m)
  (hG : ∀ᶠ n in Filter.atTop, |TwoPointAlongRay M β origin ray n| = A n * Real.exp (-(m * (n : ℝ)))) :
-- imply
  HasCorrelationLength M β origin ray m⁻¹ where xi_pos := by
-- proof
  apply StatMech.Exact3D.hasCorrelationLength_of_eventually_abs_eq_prefactor_exp M β origin ray hA hlogA hm hG

/--
[hasCorrelationLength_of_eventually_abs_between_prefactor_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ExponentialDecayCriteria.lean)
-/
@[path]
private lemma hasCorrelationLength_of_eventually_abs_between_prefactor_exp_eq
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {Alo Ahi : ℕ → ℝ}
  {m : ℝ}
-- given
  (hlo_pos : ∀ᶠ n in Filter.atTop, 0 < Alo n)
  (hhi_pos : ∀ᶠ n in Filter.atTop, 0 < Ahi n)
  (hlog_lo : Filter.Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ)) Filter.atTop (nhds 0))
  (hlog_hi : Filter.Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ)) Filter.atTop (nhds 0))
  (hm : 0 < m)
  (hlo : ∀ᶠ n in Filter.atTop, Alo n * Real.exp (-(m * (n : ℝ))) ≤ |TwoPointAlongRay M β origin ray n|)
  (hhi : ∀ᶠ n in Filter.atTop, |TwoPointAlongRay M β origin ray n| ≤ Ahi n * Real.exp (-(m * (n : ℝ)))) :
-- imply
  HasCorrelationLength M β origin ray m⁻¹ where xi_pos := by
-- proof
  apply StatMech.Exact3D.hasCorrelationLength_of_eventually_abs_between_prefactor_exp M β origin ray hlo_pos hhi_pos hlog_lo hlog_hi hm hlo hhi


-- created on 2026-10-23
