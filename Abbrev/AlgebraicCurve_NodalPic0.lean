import Abbrev.AlgebraicCurve_GluedPic0

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

section Nodal

variable (K : Type*) [Field K] {n m : ℕ} (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)] [∀ i, Algebra K (Fbar i)]

abbrev NodalData : Type _ := ∀ i : Fin n, Divisor K (Fbar i)

namespace NodalData

variable {K Fbar}
variable (src tgt : Fin m → Fin n) (xs : ∀ e, Place K (Fbar (src e))) (xt : ∀ e, Place K (Fbar (tgt e)))

end NodalData


end Nodal

end AlgebraicCurve
