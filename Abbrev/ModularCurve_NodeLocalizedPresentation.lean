import Mathlib
import Def.ModularCurve_NodeLocalized

set_option autoImplicit false

noncomputable section

namespace ModularCurve
namespace NodeLocalized

open MvPolynomial

section Presentation

variable (N : ℕ) [NeZero N] {L : Type*} [Field L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k) (a b : k)

abbrev evalRange : Subring (LaurentSeries L) := (modularEval N A).range


section KerLE

variable [hker : Fact (RingHom.ker (modularEval N A) ≤ RingHom.ker (pointEval A red a b))]


end KerLE

end Presentation

end NodeLocalized
end ModularCurve

end
