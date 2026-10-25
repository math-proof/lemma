import Def.ModularCurve_ModPFormFn

set_option autoImplicit false

noncomputable section

namespace ModularCurve

variable (F : Type) [Field F] (N' : ℕ) [NeZero N']

abbrev ssPlaces3 : Type :=
  {x : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F N') //
    0 < x.ord (ModularCurve.jGeomGen F N')}

abbrev SSCarrier3 : Type := (x : ssPlaces3 F N') → x.1.ResidueField

namespace SSCarrier3

variable {F N'}

end SSCarrier3

end ModularCurve

end
