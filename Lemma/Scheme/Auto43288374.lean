import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_isConnected_preimage_singleton_of_forall_connectedSpace_pullback_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isConnected_preimage_singleton_of_forall_connectedSpace_pullback_of_isAlgClosed.lean)
-/
@[path]
private lemma main
  {X Y : (Scheme : Type (u + 1))} (f : X ⟶ Y)
  (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Y), ConnectedSpace ↥(Limits.pullback f s))
  (y : ↥Y) :
  -- imply
  _root_.IsConnected (f.base ⁻¹' {y}) := by
  -- proof
  classical
  let K : Type u := ↑(Y.residueField y)
  let k : Type u := AlgebraicClosure K
  let ι : Spec (CommRingCat.of k) ⟶ Spec (Y.residueField y) := Spec.map (CommRingCat.ofHom (algebraMap K k))
  let s : Spec (CommRingCat.of k) ⟶ Y := ι ≫ Y.fromSpecResidueField y
  let _ : ConnectedSpace ↥(Limits.pullback f s) := h k s
  let hιs : Surjective ι := by
    refine ⟨fun q => ?_⟩
    let _ : Nonempty ↥(Spec (CommRingCat.of k)) := ⟨(⊥ : PrimeSpectrum k)⟩
    refine ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩
  let e : Limits.pullback (Limits.pullback.snd f (Y.fromSpecResidueField y)) ι ≅ Limits.pullback f s := Limits.pullbackLeftPullbackSndIso f (Y.fromSpecResidueField y) ι
  let π : Limits.pullback f s ⟶ f.fiber y := e.inv ≫ Limits.pullback.fst (Limits.pullback.snd f (Y.fromSpecResidueField y)) ι
  have hπ : Function.Surjective π.base := by
    have h1 : Function.Surjective (Limits.pullback.fst (Limits.pullback.snd f (Y.fromSpecResidueField y)) ι).base := (inferInstance : Surjective (Limits.pullback.fst (Limits.pullback.snd f (Y.fromSpecResidueField y)) ι)).1
    have h2 : Function.Surjective e.inv.base := e.inv.homeomorph.surjective
    show Function.Surjective (e.inv ≫ Limits.pullback.fst (Limits.pullback.snd f (Y.fromSpecResidueField y)) ι).base
    rw [Scheme.Hom.comp_base]
    apply h1.comp h2
  have hpre : _root_.IsPreconnected (Set.univ : Set ↥(f.fiber y)) := by
    have hpre' := (isPreconnected_univ (α := ↥(Limits.pullback f s))).image π.base π.base.hom.continuous.continuousOn
    rwa [Set.image_univ, hπ.range_eq] at hpre'
  have hne : (Set.univ : Set ↥(f.fiber y)).Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty ↥(Limits.pullback f s))
    refine ⟨π.base x, trivial⟩
  have huniv : _root_.IsConnected (Set.univ : Set ↥(f.fiber y)) := ⟨hne, hpre⟩
  have himg := huniv.image (fun x => ((f.fiberHomeo y) x : ↥X)) ((continuous_subtype_val.comp (f.fiberHomeo y).continuous).continuousOn)
  have hrange : (fun x => ((f.fiberHomeo y) x : ↥X)) '' Set.univ = f.base ⁻¹' {y} := by
    rw [Set.image_univ]
    ext z
    constructor
    ·
      rintro ⟨x, rfl⟩
      apply ((f.fiberHomeo y) x).2
    ·
      intro hz
      refine ⟨(f.fiberHomeo y).symm ⟨z, hz⟩, by simp⟩
  rwa [hrange] at himg


-- created on 2026-10-20
