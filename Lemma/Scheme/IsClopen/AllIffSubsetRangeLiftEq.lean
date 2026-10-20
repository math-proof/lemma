import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated.lean)
-/
@[path]
private lemma main
    {Z S : Scheme.{u}} (p : Z ⟶ S) [FormallyUnramified p] [LocallyOfFiniteType p] [IsSeparated p]
    (σ τ : S ⟶ Z) (hσ : σ ≫ p = 𝟙 S) (hτ : τ ≫ p = 𝟙 S) :
    IsClopen ((pullback.lift σ τ (hσ.trans hτ.symm) ⁻¹ᵁ (pullback.diagonal p).opensRange : S.Opens) : Set S) ∧
    ∀ {T : Scheme.{u}} (g : T ⟶ S),
      Set.range g ⊆ (pullback.lift σ τ (hσ.trans hτ.symm) ⁻¹ᵁ (pullback.diagonal p).opensRange : Set S) ↔ g ≫ σ = g ≫ τ := by
  let _ : IsOpenImmersion (pullback.diagonal p) := inferInstance
  let _ : IsClosedImmersion (pullback.diagonal p) := inferInstance
  refine ⟨⟨?_, (pullback.lift σ τ (hσ.trans hτ.symm) ⁻¹ᵁ (pullback.diagonal p).opensRange).2⟩, ?_⟩
  ·
    show IsClosed ((pullback.lift σ τ (hσ.trans hτ.symm)) ⁻¹' Set.range (pullback.diagonal p))
    exact ((pullback.diagonal p).isClosedEmbedding.isClosed_range).preimage (pullback.lift σ τ _).continuous
  · intro T g
    constructor
    · intro hg
      have hrange : Set.range (g ≫ pullback.lift σ τ (hσ.trans hτ.symm)) ⊆ Set.range (pullback.diagonal p) := by
        rintro _ ⟨t, rfl⟩
        exact hg ⟨t, rfl⟩
      let h : T ⟶ Z := IsOpenImmersion.lift (pullback.diagonal p) (g ≫ pullback.lift σ τ (hσ.trans hτ.symm)) hrange
      have hh : h ≫ pullback.diagonal p = g ≫ pullback.lift σ τ (hσ.trans hτ.symm) :=
        IsOpenImmersion.lift_fac _ _ hrange
      have h1 : h = g ≫ σ := by
        have := congrArg (· ≫ pullback.fst p p) hh
        simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst] at this
        exact this
      have h2 : h = g ≫ τ := by
        have := congrArg (· ≫ pullback.snd p p) hh
        simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd] at this
        exact this
      rw [← h1, h2]
    · intro hστ
      rintro _ ⟨t, rfl⟩
      show (pullback.lift σ τ (hσ.trans hτ.symm)) (g t) ∈ Set.range (pullback.diagonal p)
      have hfac : g ≫ pullback.lift σ τ (hσ.trans hτ.symm) = (g ≫ σ) ≫ pullback.diagonal p := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
        · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id, hστ]
      refine ⟨(g ≫ σ) t, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← hfac, Scheme.Hom.comp_apply]

-- created on 2026-10-20
