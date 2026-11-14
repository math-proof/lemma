import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.Mathlib_Algebra_Algebra_Hom
import Instance.Mathlib_Algebra_Algebra_Hom
import Class.Mathlib_Algebra_Algebra_Hom
import Structure.Mathlib_Algebra_Algebra_Hom

namespace Definitions
end Definitions

namespace SemialgHom

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

variable {φ} {A} {B} in
@[path]
private lemma map_smul (ψ : A →ₛₐ[φ] B) (m : R) (x : A) : ψ (m • x) = φ m • ψ x :=
  LinearMap.map_smul' ψ.toLinearMap m x

end SemialgHom
