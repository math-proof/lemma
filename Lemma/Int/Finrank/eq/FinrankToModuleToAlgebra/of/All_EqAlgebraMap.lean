import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct nonZeroDivisors


private noncomputable def toFrac
  {A : Type u} [CommRing A]
  {B : Type v} [CommRing B] [Algebra A B]
  {K : Type w} [Field K] [Algebra A K]
  {L : Type x} [Field L] [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] :
  K ⊗[A] B →ₐ[K] L :=
  Algebra.TensorProduct.lift (Algebra.ofId K L) (IsScalarTower.toAlgHom A B L) (fun _ _ => Commute.all _ _)

private lemma toFrac_tmul
  {A : Type u} [CommRing A]
  {B : Type v} [CommRing B] [Algebra A B]
  {K : Type w} [Field K] [Algebra A K]
  {L : Type x} [Field L] [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  (k : K) (b : B) :
-- imply
  toFrac (A := A) (B := B) (K := K) (L := L) (k ⊗ₜ b) = algebraMap K L k * algebraMap B L b := by
-- proof
  simp [toFrac, Algebra.ofId_apply]

private lemma toFrac_injective
  {A : Type u} [CommRing A]
  {B : Type v} [CommRing B] [IsDomain B] [Algebra A B]
  {K : Type w} [Field K] [Algebra A K] [IsFractionRing A K]
  {L : Type x} [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] :
-- imply
  Function.Injective (toFrac (A := A) (B := B) (K := K) (L := L)) := by
-- proof
  let _ : Algebra B (K ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let _ : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) (K ⊗[A] B) :=
    IsLocalization.tensorRight (R := A) (S := B) (nonZeroDivisors A) (A := K)
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨b, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) x
  have hf : ∀ b : B, toFrac (A := A) (algebraMap B (K ⊗[A] B) b) = algebraMap B L b := fun b => by
    rw [show algebraMap B (K ⊗[A] B) b = (1 : K) ⊗ₜ b from rfl, toFrac_tmul, map_one, one_mul]
  have hspec := IsLocalization.mk'_spec (K ⊗[A] B) b m
  have := congrArg (toFrac (A := A) (B := B) (K := K) (L := L)) hspec
  rw [map_mul, hx, zero_mul, hf] at this
  have hb : b = 0 := (IsFractionRing.injective B L) (by rw [← this, map_zero])
  show IsLocalization.mk' (K ⊗[A] B) b m = 0
  rw [hb, IsLocalization.mk'_zero]

private lemma toFrac_surjective
  {A : Type u} [CommRing A]
  {B : Type v} [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
  {K : Type w} [Field K] [Algebra A K] [IsFractionRing A K]
  {L : Type x} [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] :
-- imply
  Function.Surjective (toFrac (A := A) (B := B) (K := K) (L := L)) := by
-- proof
  let _ : IsDomain (K ⊗[A] B) := (toFrac_injective (A := A) (B := B) (K := K) (L := L)).isDomain
    (toFrac (A := A) (B := B) (K := K) (L := L)).toRingHom
  have hfield : IsField (K ⊗[A] B) :=
    isField_of_isIntegral_of_isField' (R := K) (S := K ⊗[A] B) (Field.toIsField K)
  let _ := hfield.toField
  intro l
  obtain ⟨b₁, b₂, hb₂, rfl⟩ := IsFractionRing.div_surjective (A := B) l
  have h2 : toFrac (A := A) (B := B) (K := K) (L := L) ((1 : K) ⊗ₜ b₂) ≠ 0 := by
    rw [toFrac_tmul, map_one, one_mul]
    apply IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb₂
  refine ⟨((1 : K) ⊗ₜ b₁) * ((1 : K) ⊗ₜ b₂)⁻¹, ?_⟩
  rw [map_mul, map_inv₀, toFrac_tmul, toFrac_tmul, map_one, one_mul, one_mul, div_eq_mul_inv]

private lemma finrank_tensor_eq
  {A : Type u} [CommRing A]
  {B : Type v} [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
  {K : Type w} [Field K] [Algebra A K] [IsFractionRing A K]
  {L : Type x} [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] :
-- imply
  Module.finrank K (K ⊗[A] B) = Module.finrank K L :=
  (AlgEquiv.ofBijective (toFrac (A := A) (B := B) (K := K) (L := L))
    ⟨toFrac_injective (A := A) (B := B) (K := K) (L := L),
      toFrac_surjective (A := A) (B := B) (K := K) (L := L)⟩).toLinearEquiv.finrank_eq


/--
[Algebra_finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite.lean)
-/
@[path]
private lemma main
  [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field F] [Field F'] [Algebra A F] [IsFractionRing A F]
  [Algebra B F'] [IsFractionRing B F']
  (φ : F →+* F')
-- given
  (hφ : ∀ a : A, algebraMap B F' (algebraMap A B a) = φ (algebraMap A F a)) :
-- imply
  Module.finrank K (K ⊗[A] B) = @Module.finrank F F' _ _ φ.toAlgebra.toModule := by
-- proof
  let _ : IsDomain B := (IsFractionRing.injective B F').isDomain (algebraMap B F')
  let e : K ≃ₐ[A] F := IsLocalization.algEquiv (nonZeroDivisors A) K F
  let _ : Algebra K F' := (φ.comp (e : K →+* F)).toAlgebra
  let _ : Algebra A F' := ((algebraMap B F').comp (algebraMap A B)).toAlgebra
  let _ : IsScalarTower A B F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let _ : IsScalarTower A K F' := IsScalarTower.of_algebraMap_eq (fun a => by
    show (algebraMap B F') (algebraMap A B a) = φ (e (algebraMap A K a))
    rw [hφ, AlgEquiv.commutes])
  rw [finrank_tensor_eq (A := A) (B := B) (K := K) (L := F')]
  let _ : Algebra F F' := φ.toAlgebra
  apply Algebra.finrank_eq_of_equiv_equiv (e : K ≃+* F) (RingEquiv.refl F') (RingHom.ext fun k => rfl)


-- created on 2026-10-13
