import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma hasOfPostcompProperty_isOpenImmersion_unramified :
  MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
    (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty (Scheme : Type (u + 1))) := by
  refine MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr ?_
  intro _ _ f hf
  obtain ⟨h₁, h₂⟩ := hf
  refine inferInstanceAs (IsOpenImmersion (pullback.diagonal f))
private lemma helper_main
  {S T : (Scheme : Type (u + 1))} (g : T ⟶ S)
  [LocallyOfFiniteType g] [FormallyUnramified g] [IsSeparated g]
  (s : S ⟶ T) (hs : s ≫ g = 𝟙 S) :
  IsOpenImmersion s ∧ IsClosedImmersion s := by
  let _ : IsOpenImmersion (s ≫ g) := by
    rw [hs]
    infer_instance
  let _ : IsClosedImmersion (s ≫ g) := by
    rw [hs]
    infer_instance
  refine ⟨hasOfPostcompProperty_isOpenImmersion_unramified.of_postcomp s g ⟨‹_›, ‹_›⟩ ‹_›,
    MorphismProperty.of_postcomp (W := @IsClosedImmersion) (W' := @IsSeparated) s g ‹_› ‹_›⟩
/--
[AlgebraicGeometry_isOpenImmersion_and_isClosedImmersion_of_comp_eq_id](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isOpenImmersion_and_isClosedImmersion_of_comp_eq_id.lean)
-/
@[path]
private lemma main
  {S T : (Scheme : Type (u + 1))} (g : T ⟶ S) [LocallyOfFiniteType g] [FormallyUnramified g] [IsSeparated g]
  (s : S ⟶ T) (hs : s ≫ g = 𝟙 S) :
  -- imply
  IsOpenImmersion s ∧ IsClosedImmersion s :=
  helper_main g s hs


-- created on 2026-10-20
