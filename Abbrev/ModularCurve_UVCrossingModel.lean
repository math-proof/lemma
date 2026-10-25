import Mathlib

set_option autoImplicit false

universe u

namespace ModularCurve

noncomputable section

abbrev uvCrossingIdeal (W : Type u) [CommRing W] (π : W) : Ideal (MvPowerSeries (Fin 2) W) :=
  Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 -
    MvPowerSeries.C π}

abbrev UVCrossingModel (W : Type u) [CommRing W] (π : W) : Type u :=
  MvPowerSeries (Fin 2) W ⧸ uvCrossingIdeal W π

namespace UVCrossingModel

variable {W : Type u} [CommRing W]

end UVCrossingModel

abbrev wittCrossingModel (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] : Type u :=
  UVCrossingModel (WittVector p k) (p : WittVector p k)

section VariableSwap

variable {W : Type u} [CommRing W]

end VariableSwap

namespace UVCrossingModel

variable {W : Type u} [CommRing W]

end UVCrossingModel

end

end ModularCurve
