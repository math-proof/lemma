import Mathlib
import Class.AlgebraicCurve_DivisorPushPull
import Structure.AlgebraicCurve_AdelicIndex
import Structure.AlgebraicCurve_PoleDivisorPackage

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve


namespace TranscendenceTower

variable (T : TranscendenceTower K E F)

abbrev xF : F := algebraMap E F T.x


end TranscendenceTower


end AlgebraicCurve

end
