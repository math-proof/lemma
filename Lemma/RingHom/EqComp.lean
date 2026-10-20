import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma S42L5.algMap_eq {R : Type*} [CommRing R] {A₁ A₂ B₁ B₂ : Type*} [CommRing A₁] [CommRing A₂] [CommRing B₁] [CommRing B₂]
    [Algebra R A₁] [Algebra R A₂] [Algebra R B₁] [Algebra R B₂]
    (f : A₁ →ₐ[R] B₁) (g : A₂ →ₐ[R] B₂) (t : A₁ ⊗[R] A₂) :
    Algebra.TensorProduct.map f g t = TensorProduct.map f.toLinearMap g.toLinearMap t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]
/--
[Bialgebra_exists_eq_comp_of_comp_eq_counit_of_ker_eq_map](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Bialgebra_exists_eq_comp_of_comp_eq_counit_of_ker_eq_map.lean)
-/
@[path]
private lemma main
    {R : Type u} [CommRing R]
    {B : Type v} [CommRing B] [Bialgebra R B]
    {G₁ : Type w} [CommRing G₁] [Bialgebra R G₁]
    {G₂ : Type x} [CommRing G₂] [Bialgebra R G₂]
    (π : B →ₐc[R] G₁) (hπ : Function.Surjective π)
    (j : G₂ →ₐc[R] B)
    (hex : RingHom.ker (π : B →ₐ[R] G₁) =
      Ideal.map (j : G₂ →ₐ[R] B) (RingHom.ker (Bialgebra.counitAlgHom R G₂)))
    (x : B →ₐc[R] B)
    (hx : (x : B →ₐ[R] B).comp (j : G₂ →ₐ[R] B) = (Algebra.ofId R B).comp (Bialgebra.counitAlgHom R G₂)) :
    ∃ y : G₁ →ₐc[R] B, x = y.comp π := by
  classical
  have hle : RingHom.ker (π : B →ₐ[R] G₁) ≤ RingHom.ker (x : B →ₐ[R] B) := by
    rw [hex, Ideal.map_le_iff_le_comap]
    intro g hg
    rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at hg
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have := AlgHom.congr_fun hx g
    simp only [AlgHom.comp_apply, Algebra.ofId_apply, Bialgebra.counitAlgHom_apply, BialgHom.coe_toAlgHom] at this
    show x (j g) = 0
    rw [this, hg, map_zero]
  let qe : (B ⧸ RingHom.ker (π : B →ₐ[R] G₁)) ≃ₐ[R] G₁ := Ideal.quotientKerAlgEquivOfSurjective hπ
  let y₀ : G₁ →ₐ[R] B :=
    (Ideal.Quotient.liftₐ (RingHom.ker (π : B →ₐ[R] G₁)) (x : B →ₐ[R] B) fun b hb => hle hb).comp (qe.symm : G₁ →ₐ[R] _)
  have hy₀ : ∀ b : B, y₀ (π b) = x b := by
    intro b
    have h1 : qe.symm (π b) = Ideal.Quotient.mk (RingHom.ker (π : B →ₐ[R] G₁)) b := by
      apply qe.injective
      rw [AlgEquiv.apply_symm_apply]
      rfl
    show Ideal.Quotient.liftₐ (RingHom.ker (π : B →ₐ[R] G₁)) (x : B →ₐ[R] B) (fun b hb => hle hb) (qe.symm (π b)) = x b
    rw [h1]
    rfl
  have hcounit : (Bialgebra.counitAlgHom R B).comp y₀ = Bialgebra.counitAlgHom R G₁ := by
    apply AlgHom.ext
    intro g
    obtain ⟨b, rfl⟩ := hπ g
    rw [AlgHom.comp_apply, hy₀, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
      CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply]
  have hcomulB : ∀ (φ : B →ₐc[R] B) (b : B), Coalgebra.comul (R := R) (φ b) =
      Algebra.TensorProduct.map (φ : B →ₐ[R] B) (φ : B →ₐ[R] B) (Coalgebra.comul (R := R) b) := by
    intro φ b; rw [S42L5.algMap_eq]; exact (CoalgHomClass.map_comp_comul_apply φ b).symm
  have hcomulπ : ∀ (b : B), Coalgebra.comul (R := R) (π b) =
      Algebra.TensorProduct.map (π : B →ₐ[R] G₁) (π : B →ₐ[R] G₁) (Coalgebra.comul (R := R) b) := by
    intro b; rw [S42L5.algMap_eq]; exact (CoalgHomClass.map_comp_comul_apply π b).symm
  have hcomul : (Algebra.TensorProduct.map y₀ y₀).comp (Bialgebra.comulAlgHom R G₁) = (Bialgebra.comulAlgHom R B).comp y₀ := by
    apply AlgHom.ext
    intro g
    obtain ⟨b, rfl⟩ := hπ g
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Bialgebra.comulAlgHom_apply, hy₀]
    erw [hcomulB x b, hcomulπ b]
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
    congr 2 <;> exact AlgHom.ext fun b' => hy₀ b'
  refine ⟨BialgHom.ofAlgHom y₀ hcounit hcomul, ?_⟩
  apply BialgHom.ext
  intro b
  exact (hy₀ b).symm

-- created on 2026-10-20
