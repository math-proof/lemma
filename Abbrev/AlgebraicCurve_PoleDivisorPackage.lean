module

public import Mathlib
public import Class.AlgebraicCurve_DivisorPushPull
public import Structure.AlgebraicCurve_AdelicIndex
public import Structure.AlgebraicCurve_PoleDivisorPackage

set_option autoImplicit false

@[expose] public noncomputable section

namespace AlgebraicCurve


namespace TranscendenceTower

variable (T : TranscendenceTower K E F)

abbrev xF : F := algebraMap E F T.x


end TranscendenceTower


end AlgebraicCurve

end
