import Mathlib
import sympy.Basic
open TensorProduct


/--
[AlgHom_liftEquiv_symm_withConv_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgHom_liftEquiv_symm_withConv_mul.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [Bialgebra R A] [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  {f g : WithConv ((S ⊗[R] A) →ₐ[S] B)} :
-- imply
  WithConv.toConv ((AlgHom.liftEquiv R S A B).symm (f * g).ofConv) =
    WithConv.toConv ((AlgHom.liftEquiv R S A B).symm f.ofConv) *
      WithConv.toConv ((AlgHom.liftEquiv R S A B).symm g.ofConv) := by
-- proof
  classical
  set F := (AlgHom.liftEquiv R S A B).symm f.ofConv with hF
  set G := (AlgHom.liftEquiv R S A B).symm g.ofConv with hG
  have hmul :
    WithConv.toConv F * WithConv.toConv G =
      WithConv.toConv ((WithConv.toConv F * WithConv.toConv G).ofConv) :=
    (WithConv.toConv_ofConv _).symm
  rw [hmul]
  congr 1
  refine AlgHom.ext fun a => ?_
  change
    LinearMap.mul' S B
      (TensorProduct.map (f.ofConv).toLinearMap (g.ofConv).toLinearMap
        (Coalgebra.comul (R := S) ((1 : S) ⊗ₜ[R] a))) =
      LinearMap.mul' R B
        (TensorProduct.map F.toLinearMap G.toLinearMap (Coalgebra.comul (R := R) a))
  rw [TensorProduct.comul_tmul, Bialgebra.comul_one]
  have key : ∀ (a₁ a₂ : A),
    (AlgebraTensorModule.tensorTensorTensorComm R S R S S S A A)
      ((1 : S ⊗[S] S) ⊗ₜ[R] (tmul R a₁ a₂)) =
      (tmul R (1 : S) a₁) ⊗ₜ[S] (tmul R (1 : S) a₂) := fun a₁ a₂ => by
    have hone : (1 : S ⊗[S] S) = (1 : S) ⊗ₜ[S] (1 : S) := rfl
    rw [hone]
    rfl
  induction Coalgebra.comul (R := R) a using TensorProduct.inductionOn with
  | tmul a₁ a₂ =>
    rw [key a₁ a₂, TensorProduct.map_tmul, LinearMap.mul'_apply,
      TensorProduct.map_tmul, LinearMap.mul'_apply,
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply]
    rfl
  | add x y hx hy =>
    rw [TensorProduct.tmul_add, map_add, map_add, map_add, map_add, map_add, hx, hy]


-- created on 2026-10-10
