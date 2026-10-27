import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma locallyQuasiFinite_of_formallyUnramified
  {X Y : Scheme} (f : X ⟶ Y)
  [FormallyUnramified f] [LocallyOfFiniteType f] :
-- imply
  LocallyQuasiFinite f := by
-- proof
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h₁ : RingHom.FormallyUnramified (f.appLE U V e).hom :=
    HasRingHomProperty.appLE (P := @FormallyUnramified) f inferInstance U V e
  have h₂ : RingHom.FiniteType (f.appLE U V e).hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f inferInstance U V e
  algebraize [(f.appLE U V e).hom]
  rw [RingHom.QuasiFinite]
  have : Algebra.EssFiniteType (Y.presheaf.obj (Opposite.op U)) (X.presheaf.obj (Opposite.op V)) :=
    Algebra.EssFiniteType.of_finiteType _ _
  infer_instance

private lemma isFinite_of_etale
  {k : Type u} [Field k]
  {X : Scheme} (f : X ⟶ Spec (CommRingCat.of k)) [Etale f] [QuasiCompact f] :
-- imply
  IsFinite f := by
-- proof
  have hlqf : LocallyQuasiFinite f := locallyQuasiFinite_of_formallyUnramified f
  have hArt : IsLocallyArtinian (Spec (CommRingCat.of k)) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr (inferInstanceAs (IsArtinianRing k))
  apply IsFinite.of_locallyQuasiFinite f

/--
[AlgebraicGeometry_IsFinite_of_smoothOfRelativeDimension_zero_of_field](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsFinite_of_smoothOfRelativeDimension_zero_of_field.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k]
  {X : Scheme} {f : X ⟶ Spec (CommRingCat.of k)}
-- given
  [SmoothOfRelativeDimension 0 f] [QuasiCompact f] :
-- imply
  IsFinite f := by
-- proof
  let _ : Etale f := (Etale.iff_smoothOfRelativeDimension_zero (f := f)).mpr inferInstance
  apply isFinite_of_etale f


-- created on 2026-10-20
