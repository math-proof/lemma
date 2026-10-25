import Mathlib

section

namespace IsLocalization


section

open TensorProduct

variable {A : Type*} [CommSemiring A] (S : Submonoid A)
  (B : Type*) [CommSemiring B] [Algebra A B]
  (K : Type*) [CommSemiring K] [Algebra A K] [IsLocalization S K]
  (L : Type*) [CommSemiring L] [Algebra B L] [Algebra A L] [Algebra K L] [IsScalarTower A B L]
    [IsScalarTower A K L] [IsLocalizedModule (M := B) (M' := L) S (Algebra.linearMap B L)]
  (M : Type*) [AddCommMonoid M] [Module K M]
  (P : Type*) [AddCommMonoid P] [Module K P]

include S in

@[simps!]
noncomputable def leftModuleTensorEquiv {R : Type*} (M' : Type*)
    [Semiring M'] [CommSemiring R] (S : Submonoid R) (A : Type*) [CommSemiring A] [Algebra R A]
    [IsLocalization S A] (M₁ : Type*) (M₂ : Type*) [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module M' M₁] [Module R M₁] [Module R M₂] [Module A M₁] [Module A M₂]
    [SMulCommClass A M' M₁] [SMulCommClass R M' M₁] [IsScalarTower R A M₁]
    [IsScalarTower R A M₂] :
    M₁ ⊗[A] M₂ ≃ₗ[M'] M₁ ⊗[R] M₂ where
  __ := IsLocalization.moduleTensorEquiv S A M₁ M₂
  map_smul' r x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m₁ m₂ => simp [TensorProduct.smul_tmul']
    | add _ _ _ _ => simp_all

end

end IsLocalization

end
