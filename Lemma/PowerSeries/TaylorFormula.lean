import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.PowerSeries.TaylorFormula
open PowerSeries


/--
[taylorFormula](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/TaylorFormula.lean)
-/
@[path]
private lemma taylorFormula_eq
  [CommRing R] [Algebra ℚ R]
  {f : PowerSeries R} :
-- imply
  (fun d : Fin 2 →₀ ℕ =>
    ((d 1).factorial : ℚ)⁻¹ •
    coeff (d 0) (d⁄dX^[d 1] f)) =
    MvPowerSeries.subst
    (fun _ : Unit =>
    MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) f := by
-- proof
  apply PowerSeries.taylorFormula f


-- created on 2026-10-20
