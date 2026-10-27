import Mathlib
import Initialize.Tactic.Attr.Basic
open Module


private noncomputable def dualMulMap
  (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
  (τ : Dual R A) :
  A →ₗ[R] Dual R A :=
  (LinearMap.mul R A).compr₂ τ

private lemma dualMulMap_apply
  (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
  (τ : Dual R A) (a x : A) :
-- imply
  dualMulMap R A τ a x = τ (a * x) :=
  rfl

private lemma coe_dualMulMap
  (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
  (τ : Dual R A) :
-- imply
  ⇑(dualMulMap R A τ) = fun a : A => τ.comp (LinearMap.mulLeft R a) := by
-- proof
  funext a
  apply LinearMap.ext
  intro x
  rfl

private lemma det_main
  (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  (b : Basis ι R A) (τ : Dual R A)
-- given
  (hτ : Function.Bijective (fun a : A => τ.comp (LinearMap.mulLeft R a))) :
-- imply
  IsUnit (Matrix.of fun i j => τ (b i * b j)).det := by
-- proof
  have hbij : Function.Bijective (dualMulMap R A τ) := by
    rwa [coe_dualMulMap]
  let e : A ≃ₗ[R] Dual R A := LinearEquiv.ofBijective (dualMulMap R A τ) hbij
  have hmat : LinearMap.toMatrix b b.dualBasis (e : A →ₗ[R] Dual R A) =
      (Matrix.of fun i j => τ (b i * b j)).transpose := by
    ext i j
    rw [LinearMap.toMatrix_apply, Basis.dualBasis_repr, Matrix.transpose_apply, Matrix.of_apply]
    show dualMulMap R A τ (b j) (b i) = τ (b j * b i)
    rfl
  have h := LinearEquiv.isUnit_det e b b.dualBasis
  rwa [hmat, Matrix.det_transpose] at h


/--
[Algebra_isUnit_det_dual_mul_of_bijective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_isUnit_det_dual_mul_of_bijective.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing A] [Algebra R A]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  {b : Basis ι R A} {τ : Dual R A}
-- given
  (hτ : Function.Bijective (fun a : A => τ.comp (LinearMap.mulLeft R a))) :
-- imply
  IsUnit (Matrix.of fun i j => τ (b i * b j)).det :=
  det_main R A b τ hτ


-- created on 2026-10-13
