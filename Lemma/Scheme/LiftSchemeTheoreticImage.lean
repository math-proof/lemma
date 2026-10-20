import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma Scheme.Hom.basicOpen_inter_closure_range_eq_empty
  {X Y : (Scheme : Type (u + 1))} (f : X ⟶ Y)
  {U : Y.Opens} (s : Y.presheaf.obj (Opposite.op U)) (hs : f.app U s = 0) :
    (Y.basicOpen s : Set Y) ∩ closure (Set.range f.base) = ∅ := by
  have hpre : (TopologicalSpace.Opens.map f.base).obj (Y.basicOpen s) = ⊥ := by
    rw [Scheme.preimage_basicOpen, hs, Scheme.basicOpen_zero]
  have hdisj : (Y.basicOpen s : Set Y) ∩ Set.range f.base = ∅ := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_empty_iff_false, iff_false, not_and,
      not_exists]
    intro hy x hx
    have : x ∈ (TopologicalSpace.Opens.map f.base).obj (Y.basicOpen s) := by
      show f.base x ∈ (Y.basicOpen s : Set Y)
      rw [hx]
      apply hy
    rwa [hpre] at this
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro y ⟨hy, hyc⟩
  have hopen : IsOpen ((Y.basicOpen s : Set Y)) := (Y.basicOpen s).isOpen
  rw [mem_closure_iff] at hyc
  obtain ⟨z, hz1, hz2⟩ := hyc _ hopen hy
  have : z ∈ (Y.basicOpen s : Set Y) ∩ Set.range f.base := ⟨hz1, hz2⟩
  rwa [hdisj] at this
private lemma Scheme.Hom.ker_le_ker_of_range_subset_closure
  {X Y T : (Scheme : Type (u + 1))} (f : X ⟶ Y) [QuasiCompact f]
  (u : T ⟶ Y) [IsReduced T] (h : Set.range u.base ⊆ closure (Set.range f.base)) :
    f.ker ≤ u.ker := by
  change f.ker ≤ Scheme.IdealSheafData.ofIdeals fun U => RingHom.ker (u.app U).hom
  rw [Scheme.IdealSheafData.le_ofIdeals_iff]
  intro U s hs
  rw [Scheme.Hom.ker_apply] at hs
  change u.app U s = 0
  apply eq_zero_of_basicOpen_eq_bot
  rw [← Scheme.preimage_basicOpen]
  ext1
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have h1 : u.base t ∈ (Y.basicOpen s : Set Y) := ht
  have h2 : u.base t ∈ closure (Set.range f.base) := h ⟨t, rfl⟩
  have := Scheme.Hom.basicOpen_inter_closure_range_eq_empty f s hs
  apply (Set.eq_empty_iff_forall_notMem.mp this) (u.base t) ⟨h1, h2⟩
/--
[AlgebraicGeometry_Scheme_Hom_exists_lift_schemeTheoreticImage_of_isReduced](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_exists_lift_schemeTheoreticImage_of_isReduced.lean)
-/
@[path]
private lemma main
  {X Y T : (Scheme : Type (u + 1))} (f : X ⟶ Y) [QuasiCompact f] (u : T ⟶ Y) [IsReduced T]
    (h : Set.range u.base ⊆ closure (Set.range f.base)) :
    ∃ v : T ⟶ f.image, v ≫ f.imageι = u := by
  refine ⟨IsClosedImmersion.lift f.imageι u ?_, IsClosedImmersion.lift_fac _ _ _⟩
  rw [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι]
  apply Scheme.Hom.ker_le_ker_of_range_subset_closure f u h


-- created on 2026-10-20
