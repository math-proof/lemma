import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma isOpen_range_diagonal
  {X Y : (Scheme : Type (u + 1))} (g : X ⟶ Y) [FormallyUnramified g] [LocallyOfFiniteType g] :
    IsOpen (Set.range (pullback.diagonal g).base) :=
  (pullback.diagonal g).isOpenEmbedding.isOpen_range

private lemma isClosed_range_diagonal
  {X Y : (Scheme : Type (u + 1))} (g : X ⟶ Y) [IsSeparated g] :
    IsClosed (Set.range (pullback.diagonal g).base) := by
  let _ : IsClosedImmersion (pullback.diagonal g) := IsSeparated.isClosedImmersion_diagonal
  apply (pullback.diagonal g).isClosedEmbedding.isClosed_range

private lemma comp_lift_eq_comp_diagonal
  {X Y : (Scheme : Type (u + 1))} (g : X ⟶ Y) {T Z : (Scheme : Type (u + 1))} (u₁ u₂ : T ⟶ X) (hg : u₁ ≫ g = u₂ ≫ g)
  (p : Z ⟶ T) (hp : p ≫ u₁ = p ≫ u₂) :
    p ≫ pullback.lift u₁ u₂ hg = (p ≫ u₁) ≫ pullback.diagonal g := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id, hp]

private lemma eq_of_comp_eq
  {X Y : (Scheme : Type (u + 1))} (g : X ⟶ Y) {T Z : (Scheme : Type (u + 1))} [FormallyUnramified g] [LocallyOfFiniteType g]
  [IsSeparated g] [PreconnectedSpace T]
  (u₁ u₂ : T ⟶ X) (hg : u₁ ≫ g = u₂ ≫ g)
  (p : Z ⟶ T) [Nonempty Z] (hp : p ≫ u₁ = p ≫ u₂) :
    u₁ = u₂ := by
  set v : T ⟶ pullback g g := pullback.lift u₁ u₂ hg with hv
  set W : Set T := Set.preimage v.base (Set.range (pullback.diagonal g).base)
  have hWclopen : IsClopen W :=
    ⟨(isClosed_range_diagonal g).preimage v.base.hom.continuous, (isOpen_range_diagonal g).preimage v.base.hom.continuous⟩
  have hWne : W.Nonempty := by
    obtain ⟨z⟩ := ‹Nonempty Z›
    refine ⟨p.base z, ?_⟩
    show v.base (p.base z) ∈ Set.range (pullback.diagonal g).base
    refine ⟨u₁.base (p.base z), ?_⟩
    have h' := congrArg (fun φ : Z ⟶ pullback g g => φ.base z) (comp_lift_eq_comp_diagonal g u₁ u₂ hg p hp)
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at h'
    apply h'.symm
  have hWuniv : W = Set.univ := by
    match isClopen_iff.mp hWclopen with
    | Or.inl h => apply absurd h hWne.ne_empty
    | Or.inr h => apply h
  have hrange : Set.range v.base ⊆ Set.range (pullback.diagonal g).base := by
    rintro _ ⟨t, rfl⟩
    change t ∈ W
    rw [hWuniv]
    apply Set.mem_univ t
  set l : T ⟶ X := IsOpenImmersion.lift (pullback.diagonal g) v hrange
  have hlv : l ≫ pullback.diagonal g = v := IsOpenImmersion.lift_fac _ _ hrange
  have h1 : u₁ = l := calc
    _ = v ≫ pullback.fst g g := by rw [hv, pullback.lift_fst]
    _ = (l ≫ pullback.diagonal g) ≫ pullback.fst g g := by rw [hlv]
    _ = l := by simp
  have h2 : u₂ = l := calc
    _ = v ≫ pullback.snd g g := by rw [hv, pullback.lift_snd]
    _ = (l ≫ pullback.diagonal g) ≫ pullback.snd g g := by rw [hlv]
    _ = l := by simp
  rw [h1, h2]

/--
[AlgebraicGeometry_eq_of_comp_eq_of_formallyUnramified_of_preconnectedSpace](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_eq_of_comp_eq_of_formallyUnramified_of_preconnectedSpace.lean)
-/
@[path]
private lemma main
  {X Y T Z : (Scheme : Type (u + 1))} (g : X ⟶ Y) [FormallyUnramified g] [LocallyOfFiniteType g]
  [IsSeparated g] [PreconnectedSpace T]
  (u₁ u₂ : T ⟶ X) (hg : u₁ ≫ g = u₂ ≫ g)
  (p : Z ⟶ T) [Nonempty Z] (hp : p ≫ u₁ = p ≫ u₂) :
    u₁ = u₂ :=
  eq_of_comp_eq g u₁ u₂ hg p hp


-- created on 2026-10-20
