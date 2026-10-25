import Mathlib
import Def.HopfAlgebra_TorsorGrading

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace HopfAlgebra.TorsorGrading

open TensorProduct

section Grading

variable (Λ : Type) [AddCommGroup Λ] [DecidableEq Λ]
variable {R H : Type} [CommRing R] [CommRing H] [Bialgebra R H]
variable (π : H →ₐc[R] MonoidAlgebra R (Multiplicative Λ))


omit [DecidableEq Λ] in
theorem gradingCoaction_apply (t : H) :
    gradingCoaction Λ π t = (LinearMap.rTensor H π.toLinearMap) ((Coalgebra.comul (R := R)) t) := rfl

theorem gradingComponents_apply (t : H) :
    gradingComponents Λ π t =
      (TensorProduct.finsuppScalarLeft R H (Multiplicative Λ))
        (((MonoidAlgebra.coeffLinearEquiv R).rTensor H) (gradingCoaction Λ π t)) := rfl

theorem componentProj_apply (j : Λ) (t : H) :
    componentProj Λ π j t = gradingComponents Λ π t (Multiplicative.ofAdd j) := rfl

theorem mem_gradedPiece_iff (j : Λ) (t : H) :
    t ∈ gradedPiece Λ π j ↔ gradingComponents Λ π t = Finsupp.single (Multiplicative.ofAdd j) t := Iff.rfl


theorem blockComponents_eq : blockComponents Λ π = gradingComponents Λ π := rfl

theorem mem_blockPiece_iff (ε : H) (j : Λ) (t : H) :
    t ∈ blockPiece Λ π ε j ↔ t ∈ gradedPiece Λ π j ∧ t * ε = t := Iff.rfl

end Grading

end HopfAlgebra.TorsorGrading

end
