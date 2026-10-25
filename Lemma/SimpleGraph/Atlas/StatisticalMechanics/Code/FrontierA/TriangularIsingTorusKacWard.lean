import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusKacWard.Part2
open StatMech StatMech.FrontierA


/--
[triangularKacWardSymbolMatrix_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusKacWard.lean)
-/
@[path]
private lemma triangularKacWardSymbolMatrix_det_eq
  {t1 t2 t3 rho z1 z2 z3 : Complex}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hz1 : z1 ≠ 0)
  (hz2 : z2 ≠ 0)
  (hz3 : z3 ≠ 0)
  (hzsum : z3 = z1 * z2) :
-- imply
  (triangularKacWardSymbolMatrix t1 t2 t3 rho z1 z2 z3).det = (1 + t1 ^ 2) * (1 + t2 ^ 2) * (1 + t3 ^ 2) + 8 * t1 * t2 * t3 - t1 * (1 - t2 ^ 2) * (1 - t3 ^ 2) * (z1 + z1⁻¹) - t2 * (1 - t1 ^ 2) * (1 - t3 ^ 2) * (z2 + z2⁻¹) - t3 * (1 - t1 ^ 2) * (1 - t2 ^ 2) * (z3 + z3⁻¹) := by
-- proof
  apply StatMech.FrontierA.triangularKacWardSymbolMatrix_det t1 t2 t3 rho z1 z2 z3 hrho hz1 hz2 hz3 hzsum


-- created on 2026-10-23
