-- Carved from Lemma/Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean: instance decls only.
import Mathlib
import Notation.Mathlib_Algebra_Algebra_Hom
import Class.Mathlib_Algebra_Algebra_Hom

section

section semialghom


variable {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)

instance instFunLike : FunLike (A →ₛₐ[φ] B) A B where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective h

end semialghom

section semialghomclass

variable (F : Type*) {R S : Type*}

instance SemialgHomClass.instSemialgHom : SemialgHomClass (A →ₛₐ[φ] B) φ A B where
  map_add ψ := ψ.map_add
  map_smulₛₗ ψ := ψ.map_smulₛₗ
  map_mul ψ := ψ.map_mul
  map_one ψ := ψ.map_one
  map_zero ψ := ψ.map_zero

instance : CoeTC F (A →ₛₐ[φ] B) :=
  ⟨SemialgHomClass.toSemialgHom⟩

end semialghomclass

end
