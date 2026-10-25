import Lemma.LanglandsTunnell.CubicInduction_PrincipalSeries3

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal

noncomputable section

namespace LanglandsTunnell.CubicInduction

section PrincipalSeries2

variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev LocalGL2 : Type := GL (Fin 2) (v.adicCompletion ℚ)

section Witness2

variable (v)

end Witness2

section UnipotentLine

variable (v)

end UnipotentLine

end PrincipalSeries2

end LanglandsTunnell.CubicInduction

end
