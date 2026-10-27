import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField.lean)
-/
@[path]
private lemma main
  {X Y : (Scheme : Type (u + 1))}
  (f : X ⟶ Y)
  (x : X)
  (m : ℕ)
  (U : Y.Opens)
  (hU : IsAffineOpen U)
  (V : X.Opens)
  (hV : IsAffineOpen V)
  (hxV : x ∈ V)
  (e : V ≤ ((TopologicalSpace.Opens.map f.base).obj U))
  (h : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension m) :
  ∃ (U' : (Spec (Y.residueField (f.base x))).Opens) (V' : (f.fiber (f.base x)).Opens) (_ : IsAffineOpen V') (_ : f.asFiber x ∈ V') (e' : V' ≤ ((TopologicalSpace.Opens.map (f.fiberToSpecResidueField (f.base x)).base).obj U')), ((f.fiberToSpecResidueField (f.base x)).appLE U' V' e').hom.IsStandardSmoothOfRelativeDimension m := by
  classical
  let P : ∀ {R S : Type u} [CommRing R] [CommRing S], RingHom R S → Prop :=
    fun g => g.IsStandardSmoothOfRelativeDimension m
  have hPi : RingHom.RespectsIso P := RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  have hPb : RingHom.IsStableUnderBaseChange P := RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange m
  set y : Y := f.base x
  let ι : Spec (Y.residueField y) ⟶ Y := Y.fromSpecResidueField y
  have hyU : y ∈ U := e hxV
  have hιU : (⊤ : (Spec (Y.residueField y)).Opens) ≤ ((TopologicalSpace.Opens.map ι.base).obj U) := by
    intro p _
    show ι.base p ∈ U
    rw [Scheme.fromSpecResidueField_apply]
    apply hyU
  have H : IsPullback (f.fiberι y) (f.fiberToSpecResidueField y) f ι := IsPullback.of_hasPullback f ι
  let V' : (f.fiber y).Opens := ((TopologicalSpace.Opens.map (f.fiberι y).base).obj V) ⊓ ((TopologicalSpace.Opens.map (f.fiberToSpecResidueField y).base).obj ⊤)
  have H' := Scheme.Hom.isPullback_resLE H hιU e (UY := V') rfl
  let _ : IsAffine U := hU
  let _ : IsAffine V := hV
  let _ : IsAffine (⊤ : (Spec (Y.residueField y)).Opens) := isAffineOpen_top (Spec (Y.residueField y))
  have h1 : P (f.resLE U V e).appTop.hom := (hPi.arrow_mk_iso_iff (arrowResLEAppIso f U V e)).mpr h
  have h2 : P (pullback.fst (ι.resLE U ⊤ hιU) (f.resLE U V e)).appTop.hom :=
    RingHom.IsStableUnderBaseChange.pullback_fst_appTop P hPb hPi _ _ h1
  let c := H'.flip.isoPullback
  have hc : c.hom ≫ pullback.fst _ _ = (f.fiberToSpecResidueField y).resLE ⊤ V' (by simp [V']) :=
    H'.flip.isoPullback_hom_fst
  let _ : IsAffine V' := IsAffine.of_isIso c.hom
  let _ : IsIso c.hom.appTop := by
    show IsIso (c.hom.app ⊤)
    infer_instance
  have h3 : P ((f.fiberToSpecResidueField y).resLE ⊤ V' (by simp [V'])).appTop.hom := by
    rw [← hc, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, hPi.cancel_right_isIso]
    apply h2
  have h4 : P ((f.fiberToSpecResidueField y).appLE ⊤ V' (by simp [V'])).hom :=
    (hPi.arrow_mk_iso_iff (arrowResLEAppIso _ ⊤ V' _)).mp h3
  refine ⟨⊤, V', ‹IsAffine V'›, ?_, by simp [V'], h4⟩
  show f.asFiber x ∈ ((TopologicalSpace.Opens.map (f.fiberι y).base).obj V) ⊓ ((TopologicalSpace.Opens.map (f.fiberToSpecResidueField y).base).obj ⊤)
  refine ⟨?_, trivial⟩
  show (f.fiberι y).base (f.asFiber x) ∈ V
  rw [Scheme.Hom.fiberι_asFiber]
  apply hxV


-- created on 2026-10-20
