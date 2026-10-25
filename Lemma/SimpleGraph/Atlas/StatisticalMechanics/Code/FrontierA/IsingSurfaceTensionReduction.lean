import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionReduction.Part2
open Set Filter Topology StatMech StatMech.Ising


/--
[weakSurfaceTensionLowerBound_of_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionReduction.lean)
-/
@[path]
private lemma weakSurfaceTensionLowerBound_of_deriv_eq
  {J : ℝ}
  {M tau : ℝ → ℝ}
-- given
  (hJ : 0 ≤ J)
  (hMnonneg : ∀ beta, 0 < beta → 0 ≤ M beta)
  (hMmono : MonotoneOn M (Ioi 0))
  (htauCont : ContinuousOn tau (Ici 0))
  (htauDiff : DifferentiableOn ℝ tau (Ioi 0))
  (hderiv : ∀ beta, 0 < beta → 2 * J * (M beta) ^ 2 ≤ deriv tau beta) :
-- imply
  HasWeakSurfaceTensionLowerBound J M tau := by
-- proof
  apply StatMech.Ising.weakSurfaceTensionLowerBound_of_deriv J M tau hJ hMnonneg hMmono htauCont htauDiff hderiv

/--
[weakSurfaceTensionLowerBound_of_pointwise_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionReduction.lean)
-/
@[path]
private lemma weakSurfaceTensionLowerBound_of_pointwise_tendsto_eq
  {J : ℝ}
  {M tau : ℝ → ℝ}
  {tauN : ℕ → ℝ → ℝ}
-- given
  (hlim : ∀ beta, Tendsto (fun n => tauN n beta) atTop (nhds (tau beta)))
  (hweak : ∀ n, HasWeakSurfaceTensionLowerBound J M (tauN n)) :
-- imply
  HasWeakSurfaceTensionLowerBound J M tau := by
-- proof
  apply StatMech.Ising.weakSurfaceTensionLowerBound_of_pointwise_tendsto J M tau tauN hlim hweak

/--
[surfaceTensionUpperBound_of_pointwise_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionReduction.lean)
-/
@[path]
private lemma surfaceTensionUpperBound_of_pointwise_tendsto_eq
  {J : ℝ}
  {M tau : ℝ → ℝ}
  {tauN : ℕ → ℝ → ℝ}
-- given
  (hlim : ∀ beta, Tendsto (fun n => tauN n beta) atTop (nhds (tau beta)))
  (hupper : ∀ n beta, 0 ≤ beta → tauN n beta ≤ 2 * J * beta * (M beta) ^ 2) :
-- imply
  ∀ beta, 0 ≤ beta → tau beta ≤ 2 * J * beta * (M beta) ^ 2 := by
-- proof
  apply StatMech.Ising.surfaceTensionUpperBound_of_pointwise_tendsto J M tau tauN hlim hupper

/--
[weakSurfaceTensionLowerBound_of_finite_deriv_and_pointwise_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionReduction.lean)
-/
@[path]
private lemma weakSurfaceTensionLowerBound_of_finite_deriv_and_pointwise_tendsto_eq
  {J : ℝ}
  {M tau : ℝ → ℝ}
  {tauN : ℕ → ℝ → ℝ}
-- given
  (hJ : 0 ≤ J)
  (hMnonneg : ∀ beta, 0 < beta → 0 ≤ M beta)
  (hMmono : MonotoneOn M (Ioi 0))
  (hlim : ∀ beta, Tendsto (fun n => tauN n beta) atTop (nhds (tau beta)))
  (htauNCont : ∀ n, ContinuousOn (tauN n) (Ici 0))
  (htauNDiff : ∀ n, DifferentiableOn ℝ (tauN n) (Ioi 0))
  (hderiv : ∀ n beta, 0 < beta → 2 * J * (M beta) ^ 2 ≤ deriv (tauN n) beta) :
-- imply
  HasWeakSurfaceTensionLowerBound J M tau := by
-- proof
  apply StatMech.Ising.weakSurfaceTensionLowerBound_of_finite_deriv_and_pointwise_tendsto J M tau tauN hJ hMnonneg hMmono hlim htauNCont htauNDiff hderiv

/--
[surfaceTension_pos_iff_ordered_of_weak_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionReduction.lean)
-/
@[path]
private lemma surfaceTension_pos_iff_ordered_of_weak_bounds_eq
  {J betaC : ℝ}
  {M tau : ℝ → ℝ}
-- given
  (hJ : 0 < J)
  (hregime : HasOrderedMagnetizationRegime M betaC)
  (htauNonneg : ∀ beta, 0 ≤ beta → 0 ≤ tau beta)
  (hupper : ∀ beta, 0 ≤ beta → tau beta ≤ 2 * J * beta * (M beta) ^ 2)
  (hweak : HasWeakSurfaceTensionLowerBound J M tau) :
-- imply
  ∀ beta, 0 ≤ beta → (0 < tau beta ↔ betaC < beta) := by
-- proof
  apply StatMech.Ising.surfaceTension_pos_iff_ordered_of_weak_bounds J betaC M tau hJ hregime htauNonneg hupper hweak

/--
[surfaceTension_pos_iff_ordered_of_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionReduction.lean)
-/
@[path]
private lemma surfaceTension_pos_iff_ordered_of_deriv_eq
  {J betaC : ℝ}
  {M tau : ℝ → ℝ}
-- given
  (hJ : 0 < J)
  (hregime : HasOrderedMagnetizationRegime M betaC)
  (hMnonneg : ∀ beta, 0 < beta → 0 ≤ M beta)
  (hMmono : MonotoneOn M (Ioi 0))
  (htauNonneg : ∀ beta, 0 ≤ beta → 0 ≤ tau beta)
  (htauCont : ContinuousOn tau (Ici 0))
  (htauDiff : DifferentiableOn ℝ tau (Ioi 0))
  (hupper : ∀ beta, 0 ≤ beta → tau beta ≤ 2 * J * beta * (M beta) ^ 2)
  (hderiv : ∀ beta, 0 < beta → 2 * J * (M beta) ^ 2 ≤ deriv tau beta) :
-- imply
  ∀ beta, 0 ≤ beta → (0 < tau beta ↔ betaC < beta) := by
-- proof
  apply StatMech.Ising.surfaceTension_pos_iff_ordered_of_deriv J betaC M tau hJ hregime hMnonneg hMmono htauNonneg htauCont htauDiff hupper hderiv

/--
[isingSurfaceTension_pos_iff_ordered_reduction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionReduction.lean)
-/
@[path]
private lemma isingSurfaceTension_pos_iff_ordered_reduction_eq
  {d : ℕ}
  {J betaC : ℝ}
  {tau : ℝ → ℝ}
-- given
  (hJ : 0 < J)
  (hregime : HasOrderedMagnetizationRegime (magnetization d) betaC)
  (hMnonneg : ∀ beta, 0 < beta → 0 ≤ magnetization d beta)
  (hMmono : MonotoneOn (magnetization d) (Ioi 0))
  (htauNonneg : ∀ beta, 0 ≤ beta → 0 ≤ tau beta)
  (htauCont : ContinuousOn tau (Ici 0))
  (htauDiff : DifferentiableOn ℝ tau (Ioi 0))
  (hupper : ∀ beta, 0 ≤ beta → tau beta ≤ 2 * J * beta * (magnetization d beta) ^ 2)
  (hderiv : ∀ beta, 0 < beta → 2 * J * (magnetization d beta) ^ 2 ≤ deriv tau beta) :
-- imply
  ∀ beta, 0 ≤ beta → (0 < tau beta ↔ betaC < beta) := by
-- proof
  apply StatMech.Ising.isingSurfaceTension_pos_iff_ordered_reduction d J betaC tau hJ hregime hMnonneg hMmono htauNonneg htauCont htauDiff hupper hderiv


-- created on 2026-10-23
