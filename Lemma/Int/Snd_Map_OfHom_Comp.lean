import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_pullback_snd_specMap_comp_of_isStableUnderBaseChange](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_pullback_snd_specMap_comp_of_isStableUnderBaseChange.lean)
-/
@[main]
private lemma main
  {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
  {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  {i : R →+* S}
  {j : S →+* T}
  {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)}
-- given
  (h : P (pullback.snd f (Spec.map (CommRingCat.ofHom i)))) :
-- imply
  P (pullback.snd f (Spec.map (CommRingCat.ofHom (j.comp i)))) := by
-- proof
  have hcomp : Spec.map (CommRingCat.ofHom (j.comp i)) =
      Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom i) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  rw [hcomp, ← pullbackLeftPullbackSndIso_inv_snd_snd f (Spec.map (CommRingCat.ofHom i)) (Spec.map (CommRingCat.ofHom j))]
  rw [P.cancel_left_of_respectsIso]
  exact P.pullback_snd _ _ h


-- created on 2026-10-05
