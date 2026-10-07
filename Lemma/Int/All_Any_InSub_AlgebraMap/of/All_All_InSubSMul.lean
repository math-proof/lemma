import Mathlib
import sympy.Basic

open scoped Pointwise

/--
[Ideal_forall_exists_sub_algebraMap_mem_of_forall_smul_eq_imp_smul_sub_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_forall_exists_sub_algebraMap_mem_of_forall_smul_eq_imp_smul_sub_mem.lean)
-/
@[main]
private lemma main
  [Group G] [Finite G]
  {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  {P : Ideal A} [P.IsMaximal]
  {Q : Ideal B} [Q.IsMaximal] [Q.LiesOver P] [Finite (B ⧸ Q)]
-- given
  (htriv : ∀ g : G, g • Q = Q → ∀ b : B, g • b - b ∈ Q) :
-- imply
  ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ Q := by
-- proof
  classical
  let : Field (A ⧸ P) := Ideal.Quotient.field P
  let : Field (B ⧸ Q) := Ideal.Quotient.field Q
  have : Module.Finite (A ⧸ P) (B ⧸ Q) := Module.Finite.of_finite
  have : IsGalois (A ⧸ P) (B ⧸ Q) := GaloisField.instIsGaloisOfFinite

  have haut : ∀ σ : (B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q), σ = AlgEquiv.refl := by
    intro σ
    obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective G P Q σ
    rw [← hg]
    apply AlgEquiv.ext
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [AlgEquiv.coe_refl, id, Ideal.Quotient.stabilizerHom_apply]
    have hgQ : (g : G) • Q = Q := g.2
    rw [Ideal.Quotient.eq]
    exact htriv g hgQ b

  have hcard : Nat.card ((B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun σ τ => (haut σ).trans (haut τ).symm⟩, ⟨AlgEquiv.refl⟩⟩
  have hrank : Module.finrank (A ⧸ P) (B ⧸ Q) = 1 := by
    rw [← IsGalois.card_aut_eq_finrank, hcard]
  intro b
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : B ⧸ Q) one_ne_zero).mp hrank (Ideal.Quotient.mk Q b)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq, ← hc, Algebra.smul_def, mul_one, Ideal.Quotient.mk_algebraMap,
    IsScalarTower.algebraMap_apply A (A ⧸ P) (B ⧸ Q) a, Ideal.Quotient.algebraMap_eq]


-- created on 2026-10-05
