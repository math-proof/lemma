import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma isIso_fiberToSpecResidueField
  {X Y Z : (Scheme : Type 1)} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
  (x : X)
  (hy : IsIso (pullback.map p (Y.fromSpecResidueField (q.base x)) q (Y.fromSpecResidueField (q.base x)) h (𝟙 _) (𝟙 _) (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]))) :
    IsIso (h.fiberToSpecResidueField x) := by
  set κy := Y.fromSpecResidueField (q.base x)
  set m := pullback.map p κy q κy h (𝟙 _) (𝟙 _) (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]) with hm
  let _ : IsIso m := hy
  have hm₁ : m ≫ pullback.fst q κy = pullback.fst p κy ≫ h := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd q κy = pullback.snd p κy := by
    rw [hm, pullback.lift_snd, Category.comp_id]
  have big : IsPullback (pullback.fst p κy) (m ≫ pullback.snd q κy) (h ≫ q) κy := by
    rw [hm₂, w]
    apply IsPullback.of_hasPullback p κy
  have hT : IsPullback (pullback.fst p κy) m h (pullback.fst q κy) :=
    big.of_bot hm₁.symm (IsPullback.of_hasPullback q κy)
  let a : Spec (X.residueField x) ⟶ pullback q κy :=
    pullback.lift (X.fromSpecResidueField x) (Spec.map (q.residueFieldMap x)) (q.SpecMap_residueFieldMap_fromSpecResidueField x).symm
  have ha : a ≫ pullback.fst q κy = X.fromSpecResidueField x := pullback.lift_fst _ _ _
  have hQ : IsPullback (pullback.fst m a) (pullback.snd m a) m a := IsPullback.of_hasPullback m a
  have big₂ : IsPullback (pullback.fst m a ≫ pullback.fst p κy) (pullback.snd m a) h (X.fromSpecResidueField x) := by
    rw [← ha]
    apply hQ.paste_horiz hT
  obtain ⟨e, he⟩ : ∃ e : pullback m a ≅ pullback h (X.fromSpecResidueField x), e.hom ≫ pullback.snd h (X.fromSpecResidueField x) = pullback.snd m a :=
    ⟨big₂.isoPullback, big₂.isoPullback_hom_snd⟩
  have hsnd : pullback.snd h (X.fromSpecResidueField x) = e.inv ≫ pullback.snd m a := by
    rw [← he, Iso.inv_hom_id_assoc]
  show IsIso (pullback.snd h (X.fromSpecResidueField x))
  rw [hsnd]
  infer_instance

/--
[AlgebraicGeometry_isIso_fiberToSpecResidueField_and_exists_isFinite_morphismRestrict_of_isIso_pullbackMap_fromSpecResidueField](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isIso_fiberToSpecResidueField_and_exists_isFinite_morphismRestrict_of_isIso_pullbackMap_fromSpecResidueField.lean)
-/
@[path]
private lemma main
  {X Y Z : (Scheme : Type 1)} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
  [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
  [IsProper q] [Flat q] [LocallyOfFinitePresentation q]
  (y : Y) (hy : IsIso (pullback.map p (Y.fromSpecResidueField y) q (Y.fromSpecResidueField y) h (𝟙 _) (𝟙 _) (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]))) :
    (∀ x : X, q.base x = y → IsIso (h.fiberToSpecResidueField x)) ∧ ∃ V : Y.Opens, y ∈ V ∧ IsFinite (morphismRestrict h ((TopologicalSpace.Opens.map q.base).obj V)) := by
  have hfib : ∀ x : X, q.base x = y → IsIso (h.fiberToSpecResidueField x) := by
    intro x hx
    subst hx
    apply isIso_fiberToSpecResidueField p q h w x hy
  refine ⟨hfib, ?_⟩
  let _ : IsProper (h ≫ q) := by
    rw [w]
    infer_instance
  let _ : IsProper h := IsProper.of_comp h q
  have hqf : ∀ z : Z, p.base z = y → h.QuasiFiniteAt z := by
    intro z hz
    have hqz : q.base (h.base z) = y := by
      rw [← hz, ← w, Scheme.Hom.comp_base]
      rfl
    let _ := hfib (h.base z) hqz
    have : Finite (h.fiber (h.base z)) :=
      Finite.of_equiv _ (Scheme.homeoOfIso (asIso (h.fiberToSpecResidueField (h.base z)))).symm.toEquiv
    apply Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)
  let V : Y.Opens := ⟨((Set.image p.base ((h.quasiFiniteLocus : Set Z)ᶜ))ᶜ), (p.isClosedMap _ h.quasiFiniteLocus.isOpen.isClosed_compl).isOpen_compl⟩
  refine ⟨V, ?_, ?_⟩
  ·
    rintro ⟨z, hz, hzy⟩
    apply hz (hqf z hzy)
  ·
    suffices LocallyQuasiFinite (morphismRestrict h ((TopologicalSpace.Opens.map q.base).obj V)) from .of_isProper_of_locallyQuasiFinite _
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
    rw [eq_top_iff]
    rintro z _
    rw [Scheme.Hom.mem_quasiFiniteLocus]
    have hz : h.QuasiFiniteAt ((Scheme.Opens.ι ((TopologicalSpace.Opens.map h.base).obj ((TopologicalSpace.Opens.map q.base).obj V))).base z) := by
      by_contra H
      apply z.2
      refine ⟨z.1, H, ?_⟩
      rw [← w, Scheme.Hom.comp_base]
      rfl
    rw [← Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion, ← morphismRestrict_ι, Scheme.Hom.quasiFiniteAt_comp_iff] at hz
    apply hz


-- created on 2026-10-20
