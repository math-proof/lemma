import Mathlib
import Lemma.AlgebraicCurve.Repartitions
import Structure.AlgebraicCurve_AdelicIndex

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]


abbrev ell (D : Divisor K F) : ℕ := Module.finrank K (LSpace D)

variable {D E : Divisor K F}


end AlgebraicCurve

end
