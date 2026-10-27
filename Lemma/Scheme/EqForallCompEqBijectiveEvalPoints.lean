import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma helper_main
  (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  (A : Type) [CommRing A] [HopfAlgebra (↥(IntermediateField.fixedField D)) A]
  {u u' : A →ₐ[↥(IntermediateField.fixedField D)] A}
  -- given
  (hev : Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId (AlgebraicClosure ℚ) (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ)) (AlgHom.pi (↥(IntermediateField.fixedField D)) _ fun ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) => (WithConv.ofConv ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)) (fun _ _ => Commute.all _ _) : AlgebraicClosure ℚ ⊗[↥(IntermediateField.fixedField D)] A →ₐ[AlgebraicClosure ℚ] (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ)))
  (h : ∀ ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ, ν.comp u = ν.comp u') :
  -- imply
  u = u' := by
  -- proof
  set L := Algebra.TensorProduct.lift (Algebra.ofId (AlgebraicClosure ℚ) (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ)) (AlgHom.pi (↥(IntermediateField.fixedField D)) _ fun ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) => (WithConv.ofConv ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)) (fun _ _ => Commute.all _ _) with hL
  have hLinc : ∀ a : A, L (Algebra.TensorProduct.includeRight a) = fun ν => (WithConv.ofConv ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) a := by
    intro a
    simp [hL, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul]
    rfl
  apply AlgHom.ext
  intro a
  apply Algebra.TensorProduct.includeRight_injective (algebraMap (↥(IntermediateField.fixedField D)) (AlgebraicClosure ℚ)).injective
  apply hev.1
  rw [hLinc, hLinc]
  funext ν
  apply DFunLike.congr_fun (h (WithConv.ofConv ν)) a

/--
[HopfAlgebra_algHom_eq_of_forall_comp_eq_of_bijective_evalPoints](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfAlgebra_algHom_eq_of_forall_comp_eq_of_bijective_evalPoints.lean)
-/
@[path]
private lemma main
  (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  (A : Type) [CommRing A] [HopfAlgebra (↥(IntermediateField.fixedField D)) A]
  [Module.Finite (↥(IntermediateField.fixedField D)) A]
  [Finite (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))]
  {u u' : A →ₐ[↥(IntermediateField.fixedField D)] A}
  -- given
  (hev : Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId (AlgebraicClosure ℚ) (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ)) (AlgHom.pi (↥(IntermediateField.fixedField D)) _ fun ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) => (WithConv.ofConv ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)) (fun _ _ => Commute.all _ _) : AlgebraicClosure ℚ ⊗[↥(IntermediateField.fixedField D)] A →ₐ[AlgebraicClosure ℚ] (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ)))
  (h : ∀ ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ, ν.comp u = ν.comp u') :
  -- imply
  u = u' := by
  -- proof
  apply helper_main D A hev h


-- created on 2026-10-20
