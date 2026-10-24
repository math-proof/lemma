import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi

universe u₁ u₂ u₃ u₄

open scoped TensorProduct

namespace Algebra.TensorProduct

variable (A : Type u₁) (R : Type u₂) (B : Type u₃) (G : Type u₄)
variable [CommRing A] [CommRing R] [CommRing B] [Algebra A R] [Algebra A B]
variable [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

@[reducible] def rightMulSemiringAction : MulSemiringAction G (R ⊗[A] B) where
  smul g x :=
    Algebra.TensorProduct.map (AlgHom.id A R) (MulSemiringAction.toAlgEquiv A B g).toAlgHom x
  one_smul x := by
    show Algebra.TensorProduct.map (AlgHom.id A R)
      (MulSemiringAction.toAlgEquiv A B (1 : G)).toAlgHom x = x
    refine TensorProduct.induction_on x (by simp) (fun r b => by simp)
      (fun y z hy hz => by simp only [map_add, hy, hz])
  mul_smul g₁ g₂ x := by
    show Algebra.TensorProduct.map (AlgHom.id A R)
        (MulSemiringAction.toAlgEquiv A B (g₁ * g₂)).toAlgHom x =
      Algebra.TensorProduct.map (AlgHom.id A R) (MulSemiringAction.toAlgEquiv A B g₁).toAlgHom
        (Algebra.TensorProduct.map (AlgHom.id A R)
          (MulSemiringAction.toAlgEquiv A B g₂).toAlgHom x)
    refine TensorProduct.induction_on x (by simp) (fun r b => by simp [mul_smul])
      (fun y z hy hz => by simp only [map_add, hy, hz])
  smul_zero g := map_zero _
  smul_add g x y := map_add _ x y
  smul_one g := map_one _
  smul_mul g x y := map_mul _ x y

theorem rightMulSemiringAction_smul_tmul (g : G) (r : R) (b : B) :
    letI := rightMulSemiringAction A R B G
    g • (r ⊗ₜ[A] b) = r ⊗ₜ (g • b) :=
  rfl

theorem rightMulSemiringAction_smulCommClass :
    letI := rightMulSemiringAction A R B G
    SMulCommClass G R (R ⊗[A] B) := by
  letI := rightMulSemiringAction A R B G
  refine ⟨fun g r x => ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
  congr 1
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  show g • ((r : R) ⊗ₜ[A] (1 : B)) = r ⊗ₜ[A] (1 : B)
  rw [rightMulSemiringAction_smul_tmul, smul_one]

end Algebra.TensorProduct

namespace Algebra.IsInvariant

open Algebra.TensorProduct in

theorem isInvariant_tensorProduct_of_flat
    (A : Type u₁) (R : Type u₂) (B : Type u₃) (G : Type u₄)
    [CommRing A] [CommRing R] [CommRing B] [Algebra A R] [Algebra A B]
    [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Module.Flat A R] [Algebra.IsInvariant A B G] :
    letI := rightMulSemiringAction A R B G
    Algebra.IsInvariant R (R ⊗[A] B) G := by
  letI := rightMulSemiringAction A R B G
  cases nonempty_fintype G
  classical

  set δ : B →ₗ[A] (G → B) :=
    LinearMap.pi (fun g => (MulSemiringAction.toAlgHom A B g).toLinearMap - LinearMap.id)
    with hδ

  have hexact : Function.Exact (Algebra.linearMap A B) δ := by
    intro b
    constructor
    · intro h0
      refine Algebra.IsInvariant.isInvariant (G := G) b (fun g => ?_)
      have := congrFun h0 g
      simpa [hδ, LinearMap.pi_apply, sub_eq_zero] using this
    · rintro ⟨a, rfl⟩
      funext g
      simp only [hδ, LinearMap.pi_apply, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
        LinearMap.id_apply, Algebra.linearMap_apply, Pi.zero_apply, sub_eq_zero,
        MulSemiringAction.toAlgHom_apply]
      rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

  have hexactR := Module.Flat.lTensor_exact R hexact

  have key : ∀ (x : R ⊗[A] B) (g : G),
      TensorProduct.piRight A A R (fun _ : G => B) (LinearMap.lTensor R δ x) g =
        g • x - x := by
    intro x
    refine TensorProduct.induction_on x (by simp) (fun r b => fun g => ?_)
      (fun y z hy hz => fun g => ?_)
    · simp only [LinearMap.lTensor_tmul, TensorProduct.piRight_apply,
        TensorProduct.piRightHom_tmul, hδ, LinearMap.pi_apply, LinearMap.sub_apply,
        AlgHom.toLinearMap_apply, LinearMap.id_apply, MulSemiringAction.toAlgHom_apply,
        TensorProduct.tmul_sub, rightMulSemiringAction_smul_tmul]
    · simp only [map_add, Pi.add_apply, hy g, hz g, smul_add]
      ring
  constructor
  intro x hx

  have hx0 : LinearMap.lTensor R δ x = 0 := by
    have : _root_.TensorProduct.piRight A A R (fun _ : G => B) (LinearMap.lTensor R δ x) = 0 := by
      funext g
      simp only [Pi.zero_apply, key x g, sub_eq_zero]
      exact hx g
    exact ((_root_.TensorProduct.piRight A A R _).map_eq_zero_iff).mp this

  obtain ⟨y, hy⟩ := (hexactR x).mp hx0
  refine ⟨_root_.TensorProduct.rid A R y, ?_⟩
  have hy' : y = (_root_.TensorProduct.rid A R).symm (_root_.TensorProduct.rid A R y) := by
    rw [LinearEquiv.symm_apply_apply]
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [hy'] at hy
  rw [← hy, _root_.TensorProduct.rid_symm_apply, LinearMap.lTensor_tmul,
    Algebra.linearMap_apply, map_one]

end Algebra.IsInvariant

set_option pp.universes true in
#check @Algebra.TensorProduct.rightMulSemiringAction
set_option pp.universes true in
#check @Algebra.IsInvariant.isInvariant_tensorProduct_of_flat
#print axioms Algebra.TensorProduct.rightMulSemiringAction
#print axioms Algebra.TensorProduct.rightMulSemiringAction_smul_tmul
#print axioms Algebra.TensorProduct.rightMulSemiringAction_smulCommClass
#print axioms Algebra.IsInvariant.isInvariant_tensorProduct_of_flat
