import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma geometricallyConnected_of_pullback_snd
  {X S S' : Scheme} (f : X ⟶ S) (σ : S' ⟶ S) [Surjective σ]
  [hgc : GeometricallyConnected (pullback.snd f σ)] :
-- imply
  GeometricallyConnected f := by
-- proof
  refine ⟨fun K _ k Z a b hZ => ?_⟩
  obtain ⟨z, -⟩ := (pullback.fst k σ).surjective default
  let ι := (pullback k σ).fromSpecResidueField z
  let kL : Spec ((pullback k σ).residueField z) ⟶ Spec (.of K) := ι ≫ pullback.fst k σ
  let l' : Spec ((pullback k σ).residueField z) ⟶ S' := ι ≫ pullback.snd k σ
  have hkl : kL ≫ k = l' ≫ σ := by simp [kL, l', Category.assoc, pullback.condition]
  let _ : Surjective kL := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  have s : IsPullback (pullback.fst b kL ≫ a) (pullback.snd b kL) f (l' ≫ σ) := by
    rw [← hkl]
    exact (IsPullback.of_hasPullback b kL).paste_horiz hZ
  have hw : (pullback.fst b kL ≫ a) ≫ f = (pullback.snd b kL ≫ l') ≫ σ := by
    simp [Category.assoc]
    exact s.w
  let m : pullback b kL ⟶ pullback f σ :=
    pullback.lift (pullback.fst b kL ≫ a) (pullback.snd b kL ≫ l') hw
  have hm₁ : m ≫ pullback.fst f σ = pullback.fst b kL ≫ a := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd f σ = pullback.snd b kL ≫ l' := pullback.lift_snd _ _ _
  have s' : IsPullback (m ≫ pullback.fst f σ) (pullback.snd b kL) f (l' ≫ σ) := by
    rwa [hm₁]
  have sq : IsPullback m (pullback.snd b kL) (pullback.snd f σ) l' :=
    IsPullback.of_right s' hm₂ (IsPullback.of_hasPullback f σ)
  have hc : ConnectedSpace ↥(pullback b kL) := hgc.geometrically_connectedSpace l' m (pullback.snd b kL) sq
  exact (pullback.fst b kL).surjective.connectedSpace (pullback.fst b kL).continuous

/--
[AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective.lean)
-/
@[path]
private lemma main :
-- imply
  DescendsAlong (@GeometricallyConnected : MorphismProperty Scheme) @Surjective := by
-- proof
  refine DescendsAlong.mk' fun {X Y Z} {f} {g} _ hf hfst => ?_
  let _ : Surjective f := hf
  let _ : GeometricallyConnected (pullback.fst f g) := hfst
  let _ : GeometricallyConnected (pullback.snd g f) := by
    rw [← pullbackSymmetry_hom_comp_fst]
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected _ _).mpr hfst
  apply geometricallyConnected_of_pullback_snd g f


-- created on 2026-10-20
