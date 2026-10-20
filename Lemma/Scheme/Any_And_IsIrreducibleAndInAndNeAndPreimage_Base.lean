import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma exists_isClosed_isIrreducible_ne_singleton {T : Type*} [TopologicalSpace T] [TopologicalSpace.NoetherianSpace T]
    (p : T) (hp : ¬ IsOpen ({p} : Set T)) :
    ∃ W : Set T, IsClosed W ∧ IsIrreducible W ∧ p ∈ W ∧ W ≠ {p} := by
  by_contra h
  push Not at h
  apply hp
  set S : Set (Set T) := {C ∈ irreducibleComponents T | p ∉ C} with hS
  have hSfin : S.Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (Set.sep_subset _ _)
  have hC0 : IsClosed (⋃ C ∈ S, C) :=
    hSfin.isClosed_biUnion fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  have heq : ({p} : Set T) = (⋃ C ∈ S, C)ᶜ := by
    ext q
    simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion, exists_prop, not_exists, not_and]
    constructor
    · rintro rfl C hC
      exact hC.2
    · intro hq
      have hpD : p ∈ irreducibleComponent q := by
        by_contra hpD
        exact hq _ ⟨irreducibleComponent_mem_irreducibleComponents q, hpD⟩ mem_irreducibleComponent
      have hD := h _ isClosed_irreducibleComponent (isIrreducible_irreducibleComponent) hpD
      have : q ∈ irreducibleComponent q := mem_irreducibleComponent
      rw [hD] at this
      exact this
  rw [heq]
  exact hC0.isOpen_compl
/--
[AlgebraicGeometry_Scheme_Hom_exists_isClosed_irreducible_subset_fiber_of_not_quasiFiniteAt_monoidalV2](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_exists_isClosed_irreducible_subset_fiber_of_not_quasiFiniteAt_monoidalV2.lean)
-/
@[path]
private lemma main
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) (hx : ¬ f.QuasiFiniteAt x) :
    ∃ Z : Set X, IsClosed Z ∧ IsIrreducible Z ∧ x ∈ Z ∧ Z ≠ {x} ∧
      Z ⊆ f.base ⁻¹' closure {f.base x} := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber] at hx
  set y := f.base x with hy
  set F := f.fiber y with hF
  set x₀ : F := f.asFiber x with hx₀
  let _ : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ inferInstance
  let _ : IsLocallyNoetherian F := LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y)
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := F) (x := x₀) (U := ⊤) trivial
  let _ : IsAffine U := hU
  let _ : IsNoetherian (U : Scheme.{u}) := { }
  set u₀ : (U : Scheme.{u}) := ⟨x₀, hxU⟩ with hu₀
  have hu₀open : ¬ IsOpen ({u₀} : Set (U : Scheme.{u})) := by
    intro ho
    apply hx
    have := (U.isOpen.isOpenMap_subtype_val) _ ho
    have heq : Subtype.val '' ({u₀} : Set (U : Scheme.{u})) = ({x₀} : Set F) := by
      apply Set.Subset.antisymm
      · rintro _ ⟨w, hw, rfl⟩
        have hw' : w = u₀ := Set.eq_of_mem_singleton hw
        rw [hw']
        exact Set.mem_singleton _
      · intro z hz
        have hz' : z = x₀ := Set.eq_of_mem_singleton hz
        exact ⟨u₀, Set.mem_singleton _, by rw [hz']⟩
    exact heq ▸ this
  obtain ⟨W, hWc, hWi, hu₀W, hWne⟩ := exists_isClosed_isIrreducible_ne_singleton u₀ hu₀open
  set g : (U : Scheme.{u}) ⟶ X := U.ι ≫ f.fiberι y with hg
  have hginj : Function.Injective g.base := by
    intro a b hab
    have h1 : (f.fiberι y).base (U.ι.base a) = (f.fiberι y).base (U.ι.base b) := hab
    rw [← Scheme.Hom.fiberHomeo_apply, ← Scheme.Hom.fiberHomeo_apply] at h1
    have h2 := (f.fiberHomeo y).injective (Subtype.ext h1)
    exact U.ι.injective h2
  have hgx : g.base u₀ = x := by
    show (f.fiberι y).base (U.ι.base u₀) = x
    have : U.ι.base u₀ = x₀ := rfl
    rw [this]
    exact Scheme.Hom.fiberι_asFiber f x
  have hgf : ∀ a, f.base (g.base a) = y := by
    intro a
    have : g.base a ∈ Set.range (f.fiberι y).base := ⟨U.ι.base a, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  refine ⟨closure (g.base '' W), isClosed_closure, (hWi.image g.base g.continuous.continuousOn).closure,
    subset_closure ⟨u₀, hu₀W, hgx⟩, ?_, ?_⟩
  · intro hZ
    obtain ⟨w, hwW, hwne⟩ : ∃ w ∈ W, w ≠ u₀ := by
      by_contra hall
      push Not at hall
      apply hWne
      exact Set.Subset.antisymm (fun w hw => hall w hw) (Set.singleton_subset_iff.mpr hu₀W)
    have hmem : g.base w ∈ closure (g.base '' W) := subset_closure ⟨w, hwW, rfl⟩
    rw [hZ, Set.mem_singleton_iff, ← hgx] at hmem
    exact hwne (hginj hmem)
  · refine closure_minimal ?_ ((isClosed_closure).preimage f.continuous)
    rintro _ ⟨a, -, rfl⟩
    change f.base (g.base a) ∈ closure {f.base x}
    rw [hgf]
    exact subset_closure rfl


-- created on 2026-10-20
