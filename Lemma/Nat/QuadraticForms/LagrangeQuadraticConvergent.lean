import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.QuadraticForms.LagrangeQuadraticConvergent
open MetaMathlibExt


/--
[lagrange_quadratic_convergent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/LagrangeQuadraticConvergent.lean)
-/
@[path]
private lemma lagrange_quadratic_convergent_eq
  {P Q R u y : ℤ}
-- given
  (hP : 0 < P)
  (hy : 0 < y)
  (hD : Q ^ 2 - 4 * P * R < 0)
  (hD3 : Q ^ 2 - 4 * P * R ≠ -3)
  (hD4 : Q ^ 2 - 4 * P * R = -4 → P ≠ 2)
  (hsol : P * u ^ 2 + Q * u * y + R * y ^ 2 = 1) :
-- imply
  let ω : ℝ := by
-- proof
  apply MetaMathlibExt.lagrange_quadratic_convergent P Q R u y hP hy hD hD3 hD4 hsol


-- created on 2026-10-20
