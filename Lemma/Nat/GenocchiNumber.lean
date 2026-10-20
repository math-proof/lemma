import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.GenocchiNumber
open MetaMathlibExt


/--
[genocchiPowerSeries_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GenocchiNumber.lean)
-/
@[path]
private lemma genocchiPowerSeries_eq_eq
  :
-- imply
  genocchiPowerSeries = 2 * PowerSeries.X * (PowerSeries.exp ℚ + 1)⁻¹ := by
-- proof
  apply MetaMathlibExt.genocchiPowerSeries_eq

/--
[genocchiNumber_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GenocchiNumber.lean)
-/
@[path]
private lemma genocchiNumber_eq_eq
  {n : ℕ} :
-- imply
  genocchiNumber n = (n.factorial : ℚ) * (PowerSeries.coeff n) genocchiPowerSeries := by
-- proof
  apply MetaMathlibExt.genocchiNumber_eq n


-- created on 2026-10-20
