module

public import Mathlib
public import Def.NumberTheory.GenocchiNumber

public section

open MetaMathlibExt


namespace MetaMathlibExt

/--
[genocchiPowerSeries_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GenocchiNumber.lean)
-/
public theorem genocchiPowerSeries_eq
  :
-- imply
  genocchiPowerSeries = 2 * PowerSeries.X * (PowerSeries.exp ℚ + 1)⁻¹ :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[genocchiNumber_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GenocchiNumber.lean)
-/
public theorem genocchiNumber_eq
  {n : ℕ} :
-- imply
  genocchiNumber n = (n.factorial : ℚ) * (PowerSeries.coeff n) genocchiPowerSeries :=
-- proof
  rfl

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
