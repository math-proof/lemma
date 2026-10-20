import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

instance isZariskiLocalAtTarget_geometricallyConnected :
    IsZariskiLocalAtTarget @GeometricallyConnected :=
  GeometricallyConnected.eq_geometrically ▸ inferInstance
private lemma of_span_eq_top (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    {ι : Type u} (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (h : ∀ i : ι,
      P (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f i))))))) :
    P g :=
  IsZariskiLocalAtTarget.of_openCover
    (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of R) f hf).openCover
    fun i => h i
/--
[AlgebraicGeometry_smooth_and_isSeparated_and_quasiCompact_and_surjective_and_geometricallyConnected_of_span_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_smooth_and_isSeparated_and_quasiCompact_and_surjective_and_geometricallyConnected_of_span_eq_top.lean)
-/
@[path]
private lemma main
    {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    {ι : Type u} (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (h : ∀ i : ι,
      Smooth (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f i)))))) ∧
      IsSeparated (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f i)))))) ∧
      QuasiCompact (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f i)))))) ∧
      Surjective (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f i)))))) ∧
      GeometricallyConnected (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f i))))))) :
    Smooth g ∧ IsSeparated g ∧ QuasiCompact g ∧ Surjective g ∧ GeometricallyConnected g :=
  ⟨of_span_eq_top @Smooth g f hf fun i => (h i).1,
    of_span_eq_top @IsSeparated g f hf fun i => (h i).2.1,
    of_span_eq_top @QuasiCompact g f hf fun i => (h i).2.2.1,
    of_span_eq_top @Surjective g f hf fun i => (h i).2.2.2.1,
    of_span_eq_top @GeometricallyConnected g f hf fun i => (h i).2.2.2.2⟩

-- created on 2026-10-20
