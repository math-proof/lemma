import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.FKCriticalAlgebra
open StatMech StatMech.FrontierA


/--
[dualOdds_eq_of_triangularFKCritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKCriticalAlgebra.lean)
-/
@[path]
private lemma dualOdds_eq_of_triangularFKCritical_eq
  {q y yStar : ℝ}
-- given
  (hy : y ≠ 0)
  (hdual : y * yStar = q)
  (htri : triangularFKCriticalPolynomial q y = 0) :
-- imply
  yStar = y ^ 2 + 3 * y := by
-- proof
  apply StatMech.FrontierA.dualOdds_eq_of_triangularFKCritical hy hdual htri

/--
[hexagonalFKCritical_of_dual_triangular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKCriticalAlgebra.lean)
-/
@[path]
private lemma hexagonalFKCritical_of_dual_triangular_eq
  {q y yStar : ℝ}
-- given
  (hy : y ≠ 0)
  (hdual : y * yStar = q)
  (htri : triangularFKCriticalPolynomial q y = 0) :
-- imply
  hexagonalFKCriticalPolynomial q yStar = 0 := by
-- proof
  apply StatMech.FrontierA.hexagonalFKCritical_of_dual_triangular hy hdual htri

/--
[hexagonalFKCritical_div_of_triangular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKCriticalAlgebra.lean)
-/
@[path]
private lemma hexagonalFKCritical_div_of_triangular_eq
  {q y : ℝ}
-- given
  (hy : y ≠ 0)
  (htri : triangularFKCriticalPolynomial q y = 0) :
-- imply
  hexagonalFKCriticalPolynomial q (q / y) = 0 := by
-- proof
  apply StatMech.FrontierA.hexagonalFKCritical_div_of_triangular hy htri

/--
[triangularFKCritical_of_dual_hexagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKCriticalAlgebra.lean)
-/
@[path]
private lemma triangularFKCritical_of_dual_hexagonal_eq
  {q y yStar : ℝ}
-- given
  (hyStar : yStar ≠ 0)
  (hdual : y * yStar = q)
  (hhex : hexagonalFKCriticalPolynomial q yStar = 0) :
-- imply
  triangularFKCriticalPolynomial q y = 0 := by
-- proof
  apply StatMech.FrontierA.triangularFKCritical_of_dual_hexagonal hyStar hdual hhex

/--
[triangularFKCritical_iff_hexagonal_of_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKCriticalAlgebra.lean)
-/
@[path]
private lemma triangularFKCritical_iff_hexagonal_of_dual_eq
  {q y yStar : ℝ}
-- given
  (hy : y ≠ 0)
  (hyStar : yStar ≠ 0)
  (hdual : y * yStar = q) :
-- imply
  triangularFKCriticalPolynomial q y = 0 ↔ hexagonalFKCriticalPolynomial q yStar = 0 := by
-- proof
  apply StatMech.FrontierA.triangularFKCritical_iff_hexagonal_of_dual hy hyStar hdual


-- created on 2026-10-23
