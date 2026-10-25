import Def.LanglandsTunnell_CubicInduction_TorusValues

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.CubicInduction.SphericalValues

variable (e₁ e₂ e₃ : ℂ)

abbrev IsDominant (a b c : ℤ) : Prop := b ≤ a ∧ c ≤ b

section Identities

variable {q : ℂ} (hq : q ≠ 0) (he₃ : e₃ ≠ 0)
include hq he₃

end Identities

section TorusPoints

variable (q : ℂ)

end TorusPoints

section Controls

end Controls

end LanglandsTunnell.CubicInduction.SphericalValues

end

#print axioms LanglandsTunnell.CubicInduction.SphericalValues.pieri_first
#print axioms LanglandsTunnell.CubicInduction.SphericalValues.pieri_second
#print axioms LanglandsTunnell.CubicInduction.SphericalValues.sphericalValue_natCast_zero_zero
#print axioms LanglandsTunnell.CubicInduction.SphericalValues.sphericalValue_natCast_succ_zero
#check @LanglandsTunnell.CubicInduction.SphericalValues.sphericalValue
#check @LanglandsTunnell.CubicInduction.SphericalValues.schurTwoRow
#check @LanglandsTunnell.CubicInduction.SphericalValues.pieri_first
#check @LanglandsTunnell.CubicInduction.SphericalValues.pieri_second
