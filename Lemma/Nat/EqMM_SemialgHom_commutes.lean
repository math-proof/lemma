import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.Mathlib_Algebra_Algebra_Hom
import Instance.Mathlib_Algebra_Algebra_Hom
import Class.Mathlib_Algebra_Algebra_Hom
import Structure.Mathlib_Algebra_Algebra_Hom
import Lemma.Nat.EqMM

namespace Definitions
end Definitions

namespace SemialgHom

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

@[path]
private lemma commutes (ψ : A →ₛₐ[φ] B) (r : R) :
    ψ (algebraMap R A r) = algebraMap S B (φ r) := by
  have := Nat.EqMM.semialgHom.map_smul ψ r 1
  rw [Algebra.smul_def, mul_one, map_one] at this
  rw [this, Algebra.smul_def, mul_one]

end SemialgHom
