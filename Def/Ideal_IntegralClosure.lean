module

public import Mathlib
public import Theorem.LinearMap.Localization.BaseChange

@[expose] public section

section

namespace IsDedekindDomain.HeightOneSpectrum

section BaseChange

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [Algebra.IsIntegral A B] [IsDedekindDomain B]
    [IsFractionRing B L]

variable (v : HeightOneSpectrum A)

variable {A} in

def Extension (v : HeightOneSpectrum A) := {w : HeightOneSpectrum B // w.under A = v}

omit [IsIntegralClosure B A L] in

@[reducible]
noncomputable def Extension.fintype : Fintype (Extension B v) :=
  have := Extension.finite A K L B v
  Fintype.ofFinite <| Extension B v

include K L in
omit [IsIntegralClosure B A L] [IsFractionRing B L] in
noncomputable def preimageComapFinset (S : Finset (HeightOneSpectrum A)) :
    Finset (HeightOneSpectrum B) :=
  Set.Finite.toFinset <| preimage_comap_finite A K L B S S.finite_toSet

omit [IsIntegralClosure B A L] in

end BaseChange

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain

open scoped TensorProduct

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L]

noncomputable def LinearEquivTensorProduct :
    L ≃ₗ[K] K ⊗[A] B :=
  let f := LocalizedModule.equivTensorProduct (nonZeroDivisors A) B
  have := IsIntegralClosure.isLocalization A K L B
  have : IsLocalizedModule (nonZeroDivisors A) (IsScalarTower.toAlgHom A B L).toLinearMap :=
    inferInstance
  let g : LocalizedModule (nonZeroDivisors A) B ≃ₗ[A] L := @IsLocalizedModule.iso
      _ _ (nonZeroDivisors A) _ _ _ _ _ _ (IsScalarTower.toAlgHom A B L) this
  let h := TensorProduct.congr (Localization.algEquiv (nonZeroDivisors A) K) (LinearEquiv.refl A B)
  LinearEquiv.extendScalarsOfIsLocalization (nonZeroDivisors A) K
    <| g.symm.trans (f.restrictScalars A) |>.trans h

variable (M : Type*) [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower A K M]

noncomputable def linearEquivTensorProductModule : L ⊗[K] M ≃ₗ[A] B ⊗[A] M :=
  let f₁ : L ⊗[K] M ≃ₗ[A] L ⊗[A] M := IsLocalization.moduleTensorEquiv (nonZeroDivisors A) K L M
    |>.restrictScalars A
  let f₂ : L ≃ₗ[A] B ⊗[A] K := LinearEquivTensorProduct A K L B
    |>.restrictScalars A
    |>.trans (TensorProduct.comm A K B)
  let f₃ : L ⊗[A] M ≃ₗ[A] (B ⊗[A] K) ⊗[A] M := TensorProduct.congr f₂ (LinearEquiv.refl A M)
  let f₄ : (B ⊗[A] K) ⊗[A] M ≃ₗ[A] B ⊗[A] (K ⊗[A] M) :=
    TensorProduct.assoc A B K M
  let f₅ : B ⊗[A] (K ⊗[A] M) ≃ₗ[A] B ⊗[A] M := TensorProduct.congr (LinearEquiv.refl A B)
    (IsLocalization.moduleLid (nonZeroDivisors A) K M |>.restrictScalars A)
  f₁.trans f₃ |>.trans f₄ |>.trans f₅

noncomputable def linearEquivTensorProductModuleLeft : L ⊗[K] M ≃ₗ[B] B ⊗[A] M :=
  let f₁ : L ⊗[K] M ≃ₗ[B] L ⊗[A] M :=
    IsLocalization.leftModuleTensorEquiv B (nonZeroDivisors A) K L M
  let f₂ : B ⊗[A] K ≃ₗ[B] L := {
    __ := LinearEquivTensorProduct A K L B
        |>.restrictScalars A
        |>.trans (TensorProduct.comm A K B) |>.symm
    map_smul' b x := by
      induction x with
      | tmul l m => simp [LinearEquivTensorProduct_symm_tmul, Algebra.smul_def]; ring
      | add => simp_all
    }
  let f₃ : (B ⊗[A] K) ⊗[A] M ≃ₗ[B] L ⊗[A] M :=
    TensorProduct.AlgebraTensorModule.congr f₂ (LinearEquiv.refl A M)
  let f₄ : (B ⊗[A] K) ⊗[A] M ≃ₗ[B] B ⊗[A] (K ⊗[A] M) :=
    TensorProduct.AlgebraTensorModule.assoc _ A B _ K M
  let f₅ : B ⊗[A] (K ⊗[A] M) ≃ₗ[B] B ⊗[A] M :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (IsLocalization.moduleLid (nonZeroDivisors A) K M |>.restrictScalars A)
  f₁.trans f₃.symm |>.trans f₄ |>.trans f₅

end IsDedekindDomain

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L]

include K in

end

end
