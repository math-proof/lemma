import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.PowerSeries.BellRiordanCentralCoefficient
open MetaMathlibExt


/--
[bell_riordan_central_coefficient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/BellRiordanCentralCoefficient.lean)
-/
@[path]
private lemma bell_riordan_central_coefficient_eq
  {M : BellMatrix ℤ}
  {u : PowerSeries ℤ}
  {n : ℕ}
-- given
  (hg : PowerSeries.constantCoeff M.g = 1)
  (hu₀ : PowerSeries.constantCoeff u = 0)
  (hu : (PowerSeries.X * PowerSeries.invOfUnit M.g (1 : ℤˣ)).subst u = PowerSeries.X) :
-- imply
  M.entry (2 * n) n =
    (n + 1 : ℤ) * PowerSeries.coeff (n + 1) u := by
-- proof
  apply MetaMathlibExt.bell_riordan_central_coefficient M u hg hu₀ hu n


-- created on 2026-10-20
