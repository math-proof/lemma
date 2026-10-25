import Def.LanglandsTunnell_ExplicitLift
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false

namespace LanglandsTunnell.Lift48

open FLT.ExplicitLift Matrix

abbrev Mat : Type := Matrix (Fin 2) (Fin 2) (ℤ√(-2))

abbrev GInt : Type := ℤ√(-1)

section DetUniversal

variable {M : Type*} [CommGroup M]

abbrev G48 : Submonoid Mat := Submonoid.closure ({Slift, Tlift} : Set Mat)

end DetUniversal

end LanglandsTunnell.Lift48
