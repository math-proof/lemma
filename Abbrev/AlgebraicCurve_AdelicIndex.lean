module

public import Mathlib
public import Theorem.Submodule.Repartitions
public import Structure.AlgebraicCurve_AdelicIndex

set_option autoImplicit false

@[expose] public noncomputable section

open IsDedekindDomain WithZero Module

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]



variable {D E : Divisor K F}


end AlgebraicCurve

end
