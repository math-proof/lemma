import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.TwoDim.SharpThreshold
open MeasureTheory Set Filter Topology StatMech StatMech.TwoDim


/--
[kst_theta_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SharpThreshold.lean)
-/
@[path]
private lemma kst_theta_eq_zero_iff_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  Percolation.theta d p hp = 0 ↔ Universality.percolationProbability d p hp = 0 := by
-- proof
  apply StatMech.TwoDim.kst_theta_eq_zero_iff d p hp

/--
[kst_subcriticalDensities_eq_coe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SharpThreshold.lean)
-/
@[path]
private lemma kst_subcriticalDensities_eq_coe_eq
  {d : ℕ} :
-- imply
  Universality.subcriticalDensities d = NNReal.toReal '' Percolation.subcriticalSet d := by
-- proof
  apply StatMech.TwoDim.kst_subcriticalDensities_eq_coe d

/--
[kst_criticalProbability_eq_pc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SharpThreshold.lean)
-/
@[path]
private lemma kst_criticalProbability_eq_pc_eq
  {d : ℕ} :
-- imply
  Universality.criticalProbability d = (Percolation.pc d : ℝ) := by
-- proof
  apply StatMech.TwoDim.kst_criticalProbability_eq_pc d

/--
[kst_crossProb_tendsto_zero_of_theta_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SharpThreshold.lean)
-/
@[path]
private lemma kst_crossProb_tendsto_zero_of_theta_zero_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (h : Percolation.theta d p hp = 0) :
-- imply
  Tendsto (fun n => Percolation.crossProb d p hp n) atTop (𝓝 0) := by
-- proof
  apply StatMech.TwoDim.kst_crossProb_tendsto_zero_of_theta_zero d p hp h

/--
[kst_sharpThreshold_crossingEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SharpThreshold.lean)
-/
@[path]
private lemma kst_sharpThreshold_crossingEvent_eq
  {d : ℕ}
-- given
  (hsub : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < Universality.criticalProbability d → Percolation.theta d p hp = 0) :
-- imply
  ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < Universality.criticalProbability d → Tendsto (fun n => (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (Percolation.crossingEvent d n)) atTop (𝓝 0) := by
-- proof
  apply StatMech.TwoDim.kst_sharpThreshold_crossingEvent d hsub

/--
[kst_sharpThreshold_of_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SharpThreshold.lean)
-/
@[path]
private lemma kst_sharpThreshold_of_dominated_eq
  {d : ℕ}
  {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site d)))}
  {C : ℝ}
-- given
  (hsub : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < Universality.criticalProbability d → Percolation.theta d p hp = 0)
  (hdom : ∀ (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ), (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (boxFam n) ≤ C * Percolation.crossProb d p hp n) :
-- imply
  ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < Universality.criticalProbability d → Tendsto (fun n => (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (boxFam n)) atTop (𝓝 0) := by
-- proof
  apply StatMech.TwoDim.kst_sharpThreshold_of_dominated d hsub hdom


-- created on 2026-10-23
