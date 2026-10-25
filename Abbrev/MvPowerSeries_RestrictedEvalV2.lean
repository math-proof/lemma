import Mathlib

set_option autoImplicit false

open MvPowerSeries

namespace MvPowerSeries.Restricted

universe u v w

variable {𝓞 : Type u} [CommRing 𝓞] {σ : Type v}


section Eval

variable (p : ℕ) {Y : Type w} [CommRing Y] [Algebra 𝓞 Y]

abbrev Cplt (Y : Type w) [CommRing Y] : Prop := IsAdicComplete (Ideal.span {(p : Y)}) Y

end Eval

end MvPowerSeries.Restricted
