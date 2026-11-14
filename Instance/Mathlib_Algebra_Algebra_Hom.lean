-- Carved from Lemma/Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean: instance decls only.
import Mathlib
import Notation.Mathlib_Algebra_Algebra_Hom
import Class.Mathlib_Algebra_Algebra_Hom
import Structure.Mathlib_Algebra_Algebra_Hom

section

section semialghom

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

instance instFunLike : FunLike (A →ₛₐ[φ] B) A B where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective h

end semialghom

section semialghomclass

variable {R S : Type*}
  [CommSemiring R] [CommSemiring S] (φ : R →+* S) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

instance SemialgHomClass.instSemialgHom : SemialgHomClass (A →ₛₐ[φ] B) φ A B where
  map_add ψ := ψ.map_add
  map_smulₛₗ ψ := ψ.map_smulₛₗ
  map_mul ψ := ψ.map_mul
  map_one ψ := ψ.map_one
  map_zero ψ := ψ.map_zero

variable (F : Type*) [FunLike F A B] [SemialgHomClass F φ A B]

instance : CoeTC F (A →ₛₐ[φ] B) :=
  ⟨fun f ↦ { (f : A →ₛₗ[φ] B), (f : A →+* B) with }⟩

end semialghomclass

end
