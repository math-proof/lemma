import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial KaehlerDifferential
open scoped TensorProduct


private lemma exists_eq_tmul_D_X
  [CommRing A] [CommRing S] [Algebra A S] [Algebra A[X] S] [IsScalarTower A A[X] S]
  (z : TensorProduct A[X] S (Ω[A[X]⁄A])) :
-- imply
  ∃ s : S, z = s ⊗ₜ[A[X]] D A A[X] X := by
-- proof
  induction z using TensorProduct.inductionOn with
  | tmul s ω =>
    have hω : ω = (polynomialEquiv A ω) • D A A[X] X := by
      conv_lhs => rw [← (polynomialEquiv A).symm_apply_apply ω]
      apply polynomialEquiv_symm A
    refine ⟨(polynomialEquiv A ω) • s, ?_⟩
    conv_lhs => rw [hω]
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨s₁, rfl⟩ := hx
    obtain ⟨s₂, rfl⟩ := hy
    refine ⟨s₁ + s₂, by rw [TensorProduct.add_tmul]⟩


private lemma mapBaseChange_tmul_D_X
  [CommRing A] [CommRing S] [Algebra A S] [Algebra A[X] S] [IsScalarTower A A[X] S]
  (s : S) :
-- imply
  mapBaseChange A A[X] S (s ⊗ₜ[A[X]] D A A[X] X) = s • D A S (algebraMap A[X] S X) := by
-- proof
  rw [mapBaseChange_tmul, map_D]


/--
[Algebra_FormallySmooth_formallySmooth_and_formallyUnramified_aeval_of_existsUnique_smul_D_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_FormallySmooth_formallySmooth_and_formallyUnramified_aeval_of_existsUnique_smul_D_eq.lean)
-/
@[path]
private lemma main
  {A : Type u} {S : Type v} [CommRing A] [CommRing S] [Algebra A S] [Algebra.FormallySmooth A S]
  {t : S}
-- given
  (ht : ∀ ω : Ω[S⁄A], ∃! s : S, ω = s • D A S t) :
-- imply
  (aeval t : A[X] →ₐ[A] S).toRingHom.FormallySmooth ∧ (aeval t : A[X] →ₐ[A] S).toRingHom.FormallyUnramified := by
-- proof
  let _ : Algebra A[X] S := (aeval t : A[X] →ₐ[A] S).toRingHom.toAlgebra
  have halg : ∀ p : A[X], algebraMap A[X] S p = aeval t p := fun _ => rfl
  have : IsScalarTower A A[X] S := IsScalarTower.of_algebraMap_eq fun a => by
    rw [halg, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, aeval_C]
  have hX : algebraMap A[X] S X = t := by
    rw [halg, aeval_X]
  have hinj : Function.Injective (mapBaseChange A A[X] S) := by
    intro z₁ z₂ h
    obtain ⟨s₁, rfl⟩ := exists_eq_tmul_D_X z₁
    obtain ⟨s₂, rfl⟩ := exists_eq_tmul_D_X z₂
    rw [mapBaseChange_tmul_D_X, mapBaseChange_tmul_D_X, hX] at h
    obtain ⟨s, -, hs⟩ := ht (s₁ • D A S t)
    have e1 : s₁ = s := hs s₁ rfl
    have e2 : s₂ = s := hs s₂ h
    rw [e1, e2]
  have hsurj : Function.Surjective (mapBaseChange A A[X] S) := by
    intro ω
    obtain ⟨s, hs, -⟩ := ht ω
    refine ⟨s ⊗ₜ D A A[X] X, by rw [mapBaseChange_tmul_D_X, hX, hs]⟩
  have hΩ : Subsingleton (Ω[S⁄A[X]]) := by
    refine ⟨fun ω₁ ω₂ => ?_⟩
    have hzero : ∀ ω : Ω[S⁄A[X]], ω = 0 := by
      intro ω
      obtain ⟨ω', rfl⟩ := map_surjective A A[X] S ω
      obtain ⟨z, rfl⟩ := hsurj ω'
      apply (exact_mapBaseChange_map A A[X] S).apply_apply_eq_zero
    rw [hzero ω₁, hzero ω₂]
  have hH1 : Subsingleton (Algebra.H1Cotangent A[X] S) := by
    refine ⟨fun h₁ h₂ => ?_⟩
    have hδ : ∀ h : Algebra.H1Cotangent A[X] S, Algebra.H1Cotangent.δ A A[X] S h = 0 := by
      intro h
      apply hinj
      rw [map_zero]
      apply (Algebra.H1Cotangent.exact_δ_mapBaseChange A A[X] S).apply_apply_eq_zero
    have hzero : ∀ h : Algebra.H1Cotangent A[X] S, h = 0 := by
      intro h
      obtain ⟨h', rfl⟩ := ((Algebra.H1Cotangent.exact_map_δ A A[X] S) h).mp (hδ h)
      rw [Subsingleton.elim h' 0, map_zero]
    rw [hzero h₁, hzero h₂]
  have : Algebra.FormallyEtale A[X] S := ⟨hΩ, hH1⟩
  refine ⟨(inferInstance : Algebra.FormallySmooth A[X] S), (inferInstance : Algebra.FormallyUnramified A[X] S)⟩


-- created on 2026-10-13
