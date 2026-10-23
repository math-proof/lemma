import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_Correspondence
import Lemma.P2M.Util

open AlgebraicCurve

/--
[AlgebraicCurve_finrankAlong_comp](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_finrankAlong_comp.lean)
-/
@[path]
private lemma main
  {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F'']
  {φ : F →ₐ[K] F'}
  {χ : F' →ₐ[K] F''} :
-- imply
  AlgebraicCurve.finrankAlong K (χ.comp φ) = AlgebraicCurve.finrankAlong K φ * AlgebraicCurve.finrankAlong K χ := by
-- proof
  let iφ : Algebra F F' := algebraAlong φ
  let iψ : Algebra F' F'' := algebraAlong χ
  let iψφ : Algebra F F'' := algebraAlong (χ.comp φ)
  have : IsScalarTower F F' F'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (Module.finrank_mul_finrank F F' F'').symm


-- created on 2026-10-23
