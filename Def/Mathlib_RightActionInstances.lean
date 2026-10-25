import Mathlib
import Instance.Mathlib_RightActionInstances

section

namespace TensorProduct.RightActions

noncomputable section semiring

variable (R S A B M : Type*) [CommSemiring R] [CommSemiring S] [AddCommMonoid M]
    [Algebra R S] [Module R M]
    [CommSemiring A] [Algebra R A]
    [Semiring B] [Algebra R B]

@[simp]
lemma smul_def (r : S) (m : M ⊗[R] S) :
    r • m = (TensorProduct.comm _ _ _).symm (r • (TensorProduct.comm _ _ _ m)) := rfl

@[simp] lemma algebraMap_eval (s : S) : algebraMap S (B ⊗[R] S) s = 1 ⊗ₜ s := rfl

def Algebra.TensorProduct.comm : A ⊗[R] B ≃ₐ[A] B ⊗[R] A where
  __ := _root_.Algebra.TensorProduct.comm R A B
  commutes' _ := rfl

variable {A B} in
@[simp] lemma Algebra.TensorProduct.comm_apply_tmul (a : A) (b : B) :
    Algebra.TensorProduct.comm R A B (a ⊗ₜ b) = b ⊗ₜ a := by
  rfl

@[simp] lemma Algebra.TensorProduct.comm_symm_apply_tmul (b : B) (a : A) :
    (Algebra.TensorProduct.comm R A B).symm (b ⊗ₜ a) = a ⊗ₜ b := rfl

def Module.TensorProduct.comm : A ⊗[R] M ≃ₗ[A] M ⊗[R] A where
  __ := (_root_.TensorProduct.comm R A M).toAddEquiv
  map_smul' a am := by
    induction am using TensorProduct.induction_on with
    | zero => simp only [smul_zero, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      map_zero, RingHom.id_apply]
    | tmul x y =>
        simp only [smul_tmul', smul_eq_mul, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
          LinearEquiv.coe_coe, comm_tmul, RingHom.id_apply, smul_def, comm_symm_tmul]
    | add x y hx hy =>
      simp_all only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        RingHom.id_apply, smul_def, smul_add, map_add]

variable {A N} in
@[simp] lemma Module.TensorProduct.comm_apply_tmul (a : A) (m : M) :
    Module.TensorProduct.comm R A M (a ⊗ₜ m) = m ⊗ₜ a := rfl

@[simp] lemma Module.TensorProduct.comm_symm_apply_tmul (m : M) (a : A) :
    (Module.TensorProduct.comm R A M).symm (m ⊗ₜ a) = a ⊗ₜ m := rfl

noncomputable abbrev LinearMap.baseChange (R : Type*) [CommRing R]
    (V W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (A : Type*) [CommRing A] [Algebra R A]
    (φ : V →ₗ[R] W) : V ⊗[R] A →ₗ[A] W ⊗[R] A :=
  (Module.TensorProduct.comm R A W) ∘ₗ
    (_root_.LinearMap.baseChange A φ) ∘ₗ
    (Module.TensorProduct.comm R A V).symm

@[simp]
lemma LinearMap.baseChange_id (R : Type*) [CommRing R]
    (V : Type*) [AddCommGroup V] [Module R V]
    (A : Type*) [CommRing A] [Algebra R A] :
    LinearMap.baseChange R V V A .id = .id := by
  ext
  simp

theorem LinearMap.baseChange_comp (R : Type*) [CommRing R]
    (U V W : Type*) [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (A : Type*) [CommRing A] [Algebra R A]
    (φ : U →ₗ[R] V) (ψ : V →ₗ[R] W) :
    LinearMap.baseChange R V W A ψ ∘ₗ LinearMap.baseChange R U V A φ =
    LinearMap.baseChange R U W A (ψ ∘ₗ φ) := by
  ext
  simp [_root_.LinearMap.baseChange_comp]

example (X Y) (f : X → Y) (g : Y → X) : Function.LeftInverse f g ↔ f ∘ g = id := by
  exact Function.leftInverse_iff_comp

noncomputable abbrev LinearEquiv.baseChange (R : Type*) [CommRing R]
    (V W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (A : Type*) [CommRing A] [Algebra R A]
    (φ : V ≃ₗ[R] W) : V ⊗[R] A ≃ₗ[A] W ⊗[R] A where
  __ := LinearMap.baseChange _ _ _ _ φ.toLinearMap
  invFun := LinearMap.baseChange _ _ _ _ φ.symm.toLinearMap
  left_inv := by
    intro x
    calc
    _ = (LinearMap.baseChange R W V A φ.symm ∘ₗ LinearMap.baseChange R V W A φ) x := rfl
    _ = _ := by simp [LinearMap.baseChange_comp]
  right_inv := by
    intro y
    change ((LinearMap.baseChange R V W A φ) ∘ₗ (LinearMap.baseChange R W V A φ.symm)) y = _
    simp [LinearMap.baseChange_comp]

noncomputable def AlgebraMap.baseChange (R : Type*) [CommRing R]
    (B C : Type*) [Ring B] [Algebra R B] [Ring C] [Algebra R C]
    (A : Type*) [CommRing A] [Algebra R A]
    (φ : B →ₐ[R] C) : B ⊗[R] A →ₐ[A] C ⊗[R] A where
  __ := Algebra.TensorProduct.map φ (.id R A)
  commutes' a := by simp

def Algebra.TensorProduct.basis {R : Type*} (A : Type*) {M : Type*} {ι : Type*}
    [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M] [Module R M]
    (b : Module.Basis ι R M) :
    Module.Basis ι A (M ⊗[R] A) :=
  (_root_.Algebra.TensorProduct.basis A b).map (Module.TensorProduct.comm R A M)

end semiring

noncomputable section ring

variable (R A B M : Type*) [CommRing R]
    [CommRing A] [Algebra R A]
    [Ring B] [Algebra R B]
    [AddCommGroup M] [Module R M]

end ring

end TensorProduct.RightActions
