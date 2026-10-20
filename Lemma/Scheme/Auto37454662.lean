import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_eq_of_comp_eq_of_residue_comp_eq_of_formallyUnramified](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_eq_of_comp_eq_of_residue_comp_eq_of_formallyUnramified.lean)
-/
@[path]
private lemma main
  {X Y : (Scheme : Type (u + 1))} (g : X ⟶ Y) [FormallyUnramified g] [LocallyOfFiniteType g]
  (A : Type u) [CommRing A] [IsLocalRing A] (u₁ u₂ : Spec (CommRingCat.of A) ⟶ X) (hg : u₁ ≫ g = u₂ ≫ g)
  (hres : Spec.map (CommRingCat.ofHom (residue A)) ≫ u₁ = Spec.map (CommRingCat.ofHom (residue A)) ≫ u₂) :
  -- imply
  u₁ = u₂ := by
  -- proof
  let X' : Over Y := Over.mk (u₁ ≫ g)
  let Y' : Over Y := Over.mk g
  let f' : X' ⟶ Y' := Over.homMk u₁
  let g' : X' ⟶ Y' := Over.homMk u₂ hg.symm
  have : FormallyUnramified Y'.hom := ‹_›
  have : LocallyOfFiniteType Y'.hom := ‹_›
  let e := (equalizer.ι f' g').left
  have hopen : IsOpenImmersion e := by
    refine MorphismProperty.of_isPullback ((Limits.isPullback_equalizer_prod f' g').map (Over.forget _)).flip ?_
    rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _ (Over.prodLeftIsoPullback Y' Y').hom]
    convert! (inferInstance : IsOpenImmersion (pullback.diagonal Y'.hom))
    ext1
    all_goals simp [← Over.comp_left]
  let ρ : Spec (CommRingCat.of (ResidueField A)) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (residue A))
  have hpt : closedPoint A ∈ Set.range e := by
    let U' : Over Y := Over.mk (ρ ≫ u₁ ≫ g)
    let ι' : U' ⟶ X' := Over.homMk ρ
    have hl : (equalizer.lift ι' (by ext1; exact hres)).left ≫ e = ρ := by
      rw [← Over.comp_left, equalizer.lift_ι]
      rfl
    let s : Spec (CommRingCat.of (ResidueField A)) := (⊥ : PrimeSpectrum _)
    have hρs : ρ s = closedPoint A := by
      rw [Spec.map_apply]
      apply PrimeSpectrum.comap_residue A s
    refine ⟨(equalizer.lift ι' (by ext1; exact hres)).left s, by rw [← hρs, ← hl]; rfl⟩
  have hsurj : Surjective e := ⟨fun y => (specializes_closedPoint y).mem_open e.isOpenEmbedding.isOpen_range hpt⟩
  have : IsIso e := (isIso_iff_isOpenImmersion_and_surjective e).mpr ⟨hopen, hsurj⟩
  apply (cancel_epi e).mp
  apply congrArg Over.Hom.left (equalizer.condition f' g')


-- created on 2026-10-20
