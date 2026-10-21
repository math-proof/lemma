import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma isIso_of_isClosedImmersion_of_surjective_of_isReduced
  {Z Y : (Scheme : Type (u + 1))}
  (f : Z ⟶ Y) [IsClosedImmersion f] [IsReduced Y]
  (hf : Function.Surjective f.base) :
  IsIso f := by
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot, ← le_bot_iff, ← Scheme.nilradical_eq_bot (X := Y), ← Scheme.IdealSheafData.vanishingIdeal_top, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
  have h : ((f.ker).support : Set Y) = Set.univ := by
    rw [Scheme.Hom.support_ker, Set.range_eq_univ.mpr hf, closure_univ]
  intro z _
  show z ∈ ((f.ker).support : Set Y)
  rw [h]
  trivial

private lemma isIso_stalkMap_of_isClosedImmersion_of_not_mem_range
  {Z M₁ M₂ : (Scheme : Type (u + 1))} [IsReduced Z]
  (i₁ : M₁ ⟶ Z)
  (i₂ : M₂ ⟶ Z) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
  (hcover : ∀ z : Z, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
  (y : M₁)
  (hy : i₁.base y ∉ Set.range i₂.base) :
  IsIso (i₁.stalkMap y) := by
  let Ω : Z.Opens := ⟨(Set.range i₂.base)ᶜ, (IsClosedImmersion.isClosedEmbedding i₂).isClosed_range.isOpen_compl⟩
  let _ : IsReduced (Ω : (Scheme : Type (u + 1))) := isReduced_of_isOpenImmersion Ω.ι
  have hf : Function.Surjective (pullback.snd i₁ Ω.ι).base := by
    intro z
    have hz : Ω.ι.base z ∈ Set.range i₁.base := by
      obtain h | h := hcover (Ω.ι.base z)
      · apply h
      · apply absurd h z.2
    obtain ⟨m, hm⟩ := hz
    obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback m z hm
    exact ⟨w, hw⟩
  let _ : IsIso (pullback.snd i₁ Ω.ι) := isIso_of_isClosedImmersion_of_surjective_of_isReduced _ hf
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := Ω.ι) y ⟨i₁.base y, hy⟩ rfl
  subst hw
  let hs : IsIso ((pullback.snd i₁ Ω.ι).stalkMap w) := inferInstance
  let hΩι : IsOpenImmersion Ω.ι := inferInstance
  let hΩ : IsIso (Ω.ι.stalkMap ((pullback.snd i₁ Ω.ι).base w)) :=
    inferInstanceAs (IsIso (Ω.ι.toLRSHom.stalkMap ((pullback.snd i₁ Ω.ι).base w)))
  have h1 : IsIso ((pullback.fst i₁ Ω.ι ≫ i₁).stalkMap w) := by
    rw [pullback.condition, Scheme.Hom.stalkMap_comp]
    apply @IsIso.comp_isIso _ _ _ _ _ (Ω.ι.stalkMap ((pullback.snd i₁ Ω.ι).base w)) ((pullback.snd i₁ Ω.ι).stalkMap w) hΩ hs
  rw [Scheme.Hom.stalkMap_comp] at h1
  let hf : IsIso ((pullback.fst i₁ Ω.ι).stalkMap w) := inferInstance
  apply @IsIso.of_isIso_comp_right _ _ _ _ _ (i₁.stalkMap ((pullback.fst i₁ Ω.ι).base w)) ((pullback.fst i₁ Ω.ι).stalkMap w) hf h1

/--
[AlgebraicGeometry_isIso_stalkMap_of_isClosedImmersion_of_not_mem_range](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isIso_stalkMap_of_isClosedImmersion_of_not_mem_range.lean)
-/
@[path]
private lemma main
  {Z M₁ M₂ : (Scheme : Type (u + 1))} [IsReduced Z]
  (i₁ : M₁ ⟶ Z)
  (i₂ : M₂ ⟶ Z) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
  (hcover : ∀ z : Z, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
  (y : M₁)
  (hy : i₁.base y ∉ Set.range i₂.base) :
  IsIso (i₁.stalkMap y) :=
  isIso_stalkMap_of_isClosedImmersion_of_not_mem_range i₁ i₂ hcover y hy


-- created on 2026-10-20
