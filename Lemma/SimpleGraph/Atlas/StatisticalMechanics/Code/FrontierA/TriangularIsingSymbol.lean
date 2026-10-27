import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
open MeasureTheory StatMech StatMech.FrontierA


/--
[triangularIsingHighTempSymbol_mul_cosh_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingSymbol.lean)
-/
@[path]
private lemma triangularIsingHighTempSymbol_mul_cosh_sq_eq
  {J1 J2 J3 k1 k2 : ℝ} :
-- imply
  triangularIsingHighTempSymbol J1 J2 J3 k1 k2 * (Real.cosh J1 ^ 2 * Real.cosh J2 ^ 2 * Real.cosh J3 ^ 2) = triangularIsingSymbol J1 J2 J3 k1 k2 := by
-- proof
  apply StatMech.FrontierA.triangularIsingHighTempSymbol_mul_cosh_sq J1 J2 J3 k1 k2

/--
[continuous_triangularIsingSymbol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingSymbol.lean)
-/
@[path]
private lemma continuous_triangularIsingSymbol_eq
  {J1 J2 J3 : ℝ} :
-- imply
  Continuous fun p : ℝ × ℝ => triangularIsingSymbol J1 J2 J3 p.1 p.2 := by
-- proof
  apply StatMech.FrontierA.continuous_triangularIsingSymbol J1 J2 J3

/--
[periodic_triangularIsingSymbol_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingSymbol.lean)
-/
@[path]
private lemma periodic_triangularIsingSymbol_left_eq
  {J1 J2 J3 k2 : ℝ} :
-- imply
  Function.Periodic (fun k1 => triangularIsingSymbol J1 J2 J3 k1 k2) (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierA.periodic_triangularIsingSymbol_left J1 J2 J3 k2

/--
[periodic_triangularIsingSymbol_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingSymbol.lean)
-/
@[path]
private lemma periodic_triangularIsingSymbol_right_eq
  {J1 J2 J3 k1 : ℝ} :
-- imply
  Function.Periodic (fun k2 => triangularIsingSymbol J1 J2 J3 k1 k2) (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierA.periodic_triangularIsingSymbol_right J1 J2 J3 k1

/--
[continuous_log_triangularIsingSymbol_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingSymbol.lean)
-/
@[path]
private lemma continuous_log_triangularIsingSymbol_of_pos_eq
  {J1 J2 J3 : ℝ}
-- given
  (hpos : ∀ k1 k2, 0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
-- imply
  Continuous fun p : ℝ × ℝ => Real.log (triangularIsingSymbol J1 J2 J3 p.1 p.2) := by
-- proof
  apply StatMech.FrontierA.continuous_log_triangularIsingSymbol_of_pos J1 J2 J3 hpos

/--
[periodic_log_triangularIsingSymbol_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingSymbol.lean)
-/
@[path]
private lemma periodic_log_triangularIsingSymbol_left_eq
  {J1 J2 J3 k2 : ℝ} :
-- imply
  Function.Periodic (fun k1 => Real.log (triangularIsingSymbol J1 J2 J3 k1 k2)) (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierA.periodic_log_triangularIsingSymbol_left J1 J2 J3 k2

/--
[periodic_log_triangularIsingSymbol_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingSymbol.lean)
-/
@[path]
private lemma periodic_log_triangularIsingSymbol_right_eq
  {J1 J2 J3 k1 : ℝ} :
-- imply
  Function.Periodic (fun k2 => Real.log (triangularIsingSymbol J1 J2 J3 k1 k2)) (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierA.periodic_log_triangularIsingSymbol_right J1 J2 J3 k1

/--
[integral_log_triangularIsingSymbol_right_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingSymbol.lean)
-/
@[path]
private lemma integral_log_triangularIsingSymbol_right_shift_eq
  {J1 J2 J3 k1 : ℝ} :
-- imply
  (∫ k2 in (0 : ℝ)..(2 * Real.pi), Real.log (triangularIsingSymbol J1 J2 J3 k1 k2)) = ∫ k2 in (-Real.pi)..Real.pi, Real.log (triangularIsingSymbol J1 J2 J3 k1 k2) := by
-- proof
  apply StatMech.FrontierA.integral_log_triangularIsingSymbol_right_shift J1 J2 J3 k1

/--
[integral_log_triangularIsingSymbol_square_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingSymbol.lean)
-/
@[path]
private lemma integral_log_triangularIsingSymbol_square_shift_eq
  {J1 J2 J3 : ℝ} :
-- imply
  (∫ k1 in (0 : ℝ)..(2 * Real.pi), ∫ k2 in (0 : ℝ)..(2 * Real.pi), Real.log (triangularIsingSymbol J1 J2 J3 k1 k2)) = ∫ k1 in (-Real.pi)..Real.pi, ∫ k2 in (-Real.pi)..Real.pi, Real.log (triangularIsingSymbol J1 J2 J3 k1 k2) := by
-- proof
  apply StatMech.FrontierA.integral_log_triangularIsingSymbol_square_shift J1 J2 J3

/--
[triangularIsingSymbol_riemann_tendsto_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingSymbol.lean)
-/
@[path]
private lemma triangularIsingSymbol_riemann_tendsto_of_pos_eq
  {J1 J2 J3 : ℝ}
-- given
  (hpos : ∀ k1 k2, 0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
-- imply
  Filter.Tendsto (fun L : ℕ => (2 * Real.pi / L) ^ 2 * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, Real.log (triangularIsingSymbol J1 J2 J3 (2 * Real.pi * i / L) (2 * Real.pi * j / L))) Filter.atTop (nhds (∫ k1 in (0 : ℝ)..(2 * Real.pi), ∫ k2 in (0 : ℝ)..(2 * Real.pi), Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_riemann_tendsto_of_pos J1 J2 J3 hpos

/--
[triangularIsingSymbol_riemann_tendsto_symmetric_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingSymbol.lean)
-/
@[path]
private lemma triangularIsingSymbol_riemann_tendsto_symmetric_of_pos_eq
  {J1 J2 J3 : ℝ}
-- given
  (hpos : ∀ k1 k2, 0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
-- imply
  Filter.Tendsto (fun L : ℕ => (2 * Real.pi / L) ^ 2 * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, Real.log (triangularIsingSymbol J1 J2 J3 (2 * Real.pi * i / L) (2 * Real.pi * j / L))) Filter.atTop (nhds (∫ k1 in (-Real.pi)..Real.pi, ∫ k2 in (-Real.pi)..Real.pi, Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_riemann_tendsto_symmetric_of_pos J1 J2 J3 hpos


-- created on 2026-10-23
