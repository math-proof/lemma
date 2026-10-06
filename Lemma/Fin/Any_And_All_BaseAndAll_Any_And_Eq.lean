import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_exists_fin_eq_of_isClosedImmersion_of_finite_pullback](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_fin_eq_of_isClosedImmersion_of_finite_pullback.lean)
-/
@[main]
private lemma main
  {X Y Z : Scheme.{u}}
  {i₁ : Y ⟶ X}
  {i₂ : Z ⟶ X} [IsClosedImmersion i₂] [Finite ↥(pullback i₁ i₂)] :
-- imply
  ∃ (n : ℕ) (y : Fin n → Y) (z : Fin n → Z), Function.Injective y ∧
      (∀ r, i₁.base (y r) = i₂.base (z r)) ∧
      ∀ (P : Y) (Q : Z), i₁.base P = i₂.base Q → ∃ r, P = y r ∧ Q = z r := by
-- proof
  classical
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ↥(pullback i₁ i₂)
  refine ⟨n, fun r => (pullback.fst i₁ i₂).base (e.symm r), fun r => (pullback.snd i₁ i₂).base (e.symm r), ?_, ?_, ?_⟩
  · intro r s hrs
    have hinj := (pullback.fst i₁ i₂).isClosedEmbedding.injective
    exact e.symm.injective (hinj hrs)
  · intro r
    have h := congrArg (fun φ => φ.base (e.symm r)) (pullback.condition (f := i₁) (g := i₂))
    simpa using h
  · intro P Q hPQ
    obtain ⟨t, ht1, ht2⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) P Q hPQ
    refine ⟨e t, ?_, ?_⟩
    · simp only [Equiv.symm_apply_apply]; exact ht1.symm
    · simp only [Equiv.symm_apply_apply]; exact ht2.symm


-- created on 2026-10-05
