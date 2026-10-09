import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry
open TopologicalSpace Opposite

/--
[AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_mul.lean)
-/
@[path]
private lemma main
  {X : Scheme.{u}}
  {I J : Ideal Γ(X, ⊤)} :
-- imply
  Scheme.IdealSheafData.ofIdealTop (I * J) = Scheme.IdealSheafData.ofIdealTop I * Scheme.IdealSheafData.ofIdealTop J := by
-- proof
  apply Scheme.IdealSheafData.ext
  funext U
  simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_mul]


-- created on 2026-10-03
