import Mathlib
import sympy.analysis.Misc.SI

namespace SI
open UnitsSystem

/- This is needed to keep dimensions such as `Length` and `Speed * Time` defeq to each other -/
unseal Rat.add Rat.mul Rat.sub Rat.inv

variable (m:Mass) (v:Speed) (F:Force) (p:Momentum) (E:Energy) (h:Length) (t:Time) (a:Acceleration)
abbrev half_frequency_unit := (1/2:ℚ) • frequency_unit
abbrev SqrtFrequency := Scalar half_frequency_unit
abbrev sqrt_hertz:SqrtFrequency := StandardUnit _
abbrev NNTemperature := { T:Temperature // T ≥ 0 }

end SI
