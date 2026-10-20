import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


variable {X Y : Scheme} {f : X ⟶ Y}

private lemma comp_lift_eq_comp_diagonal
  {T T₀ : Scheme} (u u' : T ⟶ X) (hf : u ≫ f = u' ≫ f)
  (j : T₀ ⟶ T) (hj : j ≫ u = j ≫ u') :
  j ≫ pullback.lift u u' hf = (j ≫ u) ≫ pullback.diagonal f := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id, hj]

private lemma eq_of_comp_eq
  {T T₀ : Scheme} [FormallyUnramified f] [LocallyOfFiniteType f]
  (j : T₀ ⟶ T) [Surjective j] (u u' : T ⟶ X) (hf : u ≫ f = u' ≫ f) (hj : j ≫ u = j ≫ u') :
  u = u' := by
  set v : T ⟶ pullback f f := pullback.lift u u' hf with hv
  have hrange : Set.range v.base ⊆ Set.range (pullback.diagonal f).base := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨t₀, rfl⟩ := j.surjective t
    refine ⟨u.base (j.base t₀), ?_⟩
    have h := comp_lift_eq_comp_diagonal u u' hf j hj
    have h' := congrArg (fun φ : T₀ ⟶ pullback f f => φ.base t₀) h
    simp [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at h'
    exact h'.symm
  set l : T ⟶ X := IsOpenImmersion.lift (pullback.diagonal f) v hrange with hl
  have hlv : l ≫ pullback.diagonal f = v := IsOpenImmersion.lift_fac _ _ hrange
  have h1 : u = l := calc
    _ = v ≫ pullback.fst f f := by rw [hv, pullback.lift_fst]
    _ = (l ≫ pullback.diagonal f) ≫ pullback.fst f f := by rw [hlv]
    _ = l := by simp
  have h2 : u' = l := calc
    _ = v ≫ pullback.snd f f := by rw [hv, pullback.lift_snd]
    _ = (l ≫ pullback.diagonal f) ≫ pullback.snd f f := by rw [hlv]
    _ = l := by simp
  rw [h1, h2]

/--
[AlgebraicGeometry_FormallyUnramified_eq_of_comp_eq_of_surjective_of_locallyOfFiniteType](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_FormallyUnramified_eq_of_comp_eq_of_surjective_of_locallyOfFiniteType.lean)
-/
@[path]
private lemma main
  {X Y T T₀ : Scheme} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
  (j : T₀ ⟶ T) [Surjective j] (u u' : T ⟶ X) (hf : u ≫ f = u' ≫ f) (hj : j ≫ u = j ≫ u') :
  u = u' :=
  eq_of_comp_eq j u u' hf hj


-- created on 2026-10-20
