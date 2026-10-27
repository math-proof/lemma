import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.MagNonneg.Part2
open MeasureTheory Filter Topology BoundedContinuousFunction StatMech StatMech.Ising


/--
[continuous_spinObs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MagNonneg.lean)
-/
@[path]
private lemma continuous_spinObs_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  Continuous (fun ω : ConfigSpace (Site d) => spin ω x) := by
-- proof
  apply StatMech.Ising.continuous_spinObs x

/--
[spinObs_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MagNonneg.lean)
-/
@[path]
private lemma spinObs_le_one_eq
  {d : ℕ}
  {x : Site d}
  {ω : ConfigSpace (Site d)} :
-- imply
  ‖spin ω x‖ ≤ 1 := by
-- proof
  apply StatMech.Ising.spinObs_le_one x ω

/--
[spinBCF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MagNonneg.lean)
-/
@[path]
private lemma spinBCF_apply_eq
  {d : ℕ}
  {x : Site d}
  {ω : ConfigSpace (Site d)} :
-- imply
  spinBCF x ω = spin ω x := by
-- proof
  apply StatMech.Ising.spinBCF_apply x ω

/--
[integral_spinBCF_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MagNonneg.lean)
-/
@[path]
private lemma integral_spinBCF_eq_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ} :
-- imply
  ∫ ω, (spinBCF (origin d)) ω ∂(plusState d β 0 : Measure (ConfigSpace (Site d))) = magnetization d β := by
-- proof
  apply StatMech.Ising.integral_spinBCF_eq d β

/--
[nonneg_integral_of_weakLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MagNonneg.lean)
-/
@[path]
private lemma nonneg_integral_of_weakLimit_eq
  {d : ℕ}
  {μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))}
  {ν : ProbabilityMeasure (ConfigSpace (Site d))}
  {f : ConfigSpace (Site d) →ᵇ ℝ}
-- given
  (h : WeakConvergesTo μ ν)
  (hpos : ∀ n, 0 ≤ ∫ ω, f ω ∂(μ n : Measure (ConfigSpace (Site d)))) :
-- imply
  0 ≤ ∫ ω, f ω ∂(ν : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.nonneg_integral_of_weakLimit h f hpos

/--
[magnetization_nonneg_of_fv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MagNonneg.lean)
-/
@[path]
private lemma magnetization_nonneg_of_fv_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
-- given
  (hfv : ∀ n, 0 ≤ ∫ ω, spin ω (origin d) ∂(plusMeasure d n β 0 : Measure (ConfigSpace (Site d)))) :
-- imply
  0 ≤ magnetization d β := by
-- proof
  apply StatMech.Ising.magnetization_nonneg_of_fv d β hfv

/--
[hmag_nonneg_of_fv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MagNonneg.lean)
-/
@[path]
private lemma hmag_nonneg_of_fv_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (hfv : ∀ β, ∀ n, 0 ≤ ∫ ω, spin ω (origin d) ∂(plusMeasure d n β 0 : Measure (ConfigSpace (Site d)))) :
-- imply
  ∀ β, 0 ≤ magnetization d β := by
-- proof
  apply StatMech.Ising.hmag_nonneg_of_fv d hfv


-- created on 2026-10-23
