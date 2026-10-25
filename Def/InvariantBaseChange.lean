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

end Algebra.TensorProduct
