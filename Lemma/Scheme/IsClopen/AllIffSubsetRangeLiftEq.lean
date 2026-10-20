import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated.lean)
-/
@[path]
private lemma main
  {Z S : (Scheme : Type (u + 1))} (p : Z ⟶ S) [FormallyUnramified p] [LocallyOfFiniteType p] [IsSeparated p]
  (σ τ : S ⟶ Z) (hσ : σ ≫ p = 𝟙 S) (hτ : τ ≫ p = 𝟙 S) :
  -- imply
  IsClopen (((TopologicalSpace.Opens.map (pullback.lift σ τ (hσ.trans hτ.symm)).base).obj (pullback.diagonal p).opensRange : S.Opens) : Set S) ∧ ∀ {T : (Scheme : Type (u + 1))} (g : T ⟶ S), Set.range g ⊆ (((TopologicalSpace.Opens.map (pullback.lift σ τ (hσ.trans hτ.symm)).base).obj (pullback.diagonal p).opensRange : S.Opens) : Set S) ↔ g ≫ σ = g ≫ τ := by
  -- proof
  let _ : IsOpenImmersion (pullback.diagonal p) := inferInstance
  let _ : IsClosedImmersion (pullback.diagonal p) := inferInstance
  refine ⟨⟨?_, ((TopologicalSpace.Opens.map (pullback.lift σ τ (hσ.trans hτ.symm)).base).obj (pullback.diagonal p).opensRange).2⟩, ?_⟩
  ·
    show IsClosed ((pullback.lift σ τ (hσ.trans hτ.symm)) ⁻¹' Set.range (pullback.diagonal p))
    apply ((pullback.diagonal p).isClosedEmbedding.isClosed_range).preimage (pullback.lift σ τ _).continuous
  ·
    intro T g
    constructor
    ·
      intro hg
      have hrange : Set.range (g ≫ pullback.lift σ τ (hσ.trans hτ.symm)) ⊆ Set.range (pullback.diagonal p) := by
        rintro _ ⟨t, rfl⟩
        apply hg ⟨t, rfl⟩
      let h : T ⟶ Z := IsOpenImmersion.lift (pullback.diagonal p) (g ≫ pullback.lift σ τ (hσ.trans hτ.symm)) hrange
      have hh : h ≫ pullback.diagonal p = g ≫ pullback.lift σ τ (hσ.trans hτ.symm) := IsOpenImmersion.lift_fac _ _ hrange
      have h1 : h = g ≫ σ := by
        have hfst := congrArg (fun q => q ≫ pullback.fst p p) hh
        simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst] at hfst
        apply hfst
      have h2 : h = g ≫ τ := by
        have hsnd := congrArg (fun q => q ≫ pullback.snd p p) hh
        simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd] at hsnd
        apply hsnd
      rw [← h1, h2]
    ·
      intro hστ
      rintro _ ⟨t, rfl⟩
      show (pullback.lift σ τ (hσ.trans hτ.symm)) (g t) ∈ Set.range (pullback.diagonal p)
      have hfac : g ≫ pullback.lift σ τ (hσ.trans hτ.symm) = (g ≫ σ) ≫ pullback.diagonal p := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
        · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id, hστ]
      refine ⟨(g ≫ σ) t, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← hfac, Scheme.Hom.comp_apply]


-- created on 2026-10-20
