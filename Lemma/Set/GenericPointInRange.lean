import Mathlib
import Initialize.Tactic.Attr.Basic
open TopologicalSpace
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[IrreducibleSpace_genericPoint_mem_range_of_denseRange](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IrreducibleSpace_genericPoint_mem_range_of_denseRange.lean)
-/
@[path]
private lemma main
  [TopologicalSpace X] [TopologicalSpace Y]
  [NoetherianSpace X] [QuasiSober X] [QuasiSober Y] [IrreducibleSpace Y] [T0Space Y]
  {f : X → Y}
  -- given
  (hf : Continuous f)
  (hd : DenseRange f) :
  -- imply
  genericPoint Y ∈ Set.range f := by
  -- proof
  classical
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  have hrange : Set.range f = ⋃ Z ∈ irreducibleComponents X, Set.image f Z := by
    rw [← Set.image_univ, ← sUnion_irreducibleComponents, Set.image_sUnion, Set.sUnion_image]
  have hcl : closure (Set.range f) = ⋃ Z ∈ irreducibleComponents X, closure (Set.image f Z) := by
    rw [hrange, hfin.closure_biUnion]
  let t : Finset (Set Y) := hfin.toFinset.image fun Z => closure (Set.image f Z)
  have hcov : (Set.univ : Set Y) ⊆ Set.sUnion (↑t : Set (Set Y)) := by
    intro y _
    have hy : y ∈ closure (Set.range f) := by
      rw [hd.closure_range]
      trivial
    rw [hcl, Set.mem_iUnion₂] at hy
    obtain ⟨Z, hZ, hyZ⟩ := hy
    refine Set.mem_sUnion.mpr ⟨closure (Set.image f Z), ?_, hyZ⟩
    simp only [t, Finset.coe_image, Set.Finite.coe_toFinset]
    refine ⟨Z, hZ, rfl⟩
  have hclosed : ∀ z, z ∈ t → IsClosed z := by
    intro z hz
    simp only [t, Finset.mem_image, Set.Finite.mem_toFinset] at hz
    obtain ⟨Z, -, rfl⟩ := hz
    apply isClosed_closure
  obtain ⟨z, hz, hz'⟩ := (isIrreducible_iff_sUnion_isClosed.mp (IrreducibleSpace.isIrreducible_univ Y)) t hclosed hcov
  simp only [t, Finset.mem_image, Set.Finite.mem_toFinset] at hz
  obtain ⟨Z, hZ, rfl⟩ := hz
  have hgen : IsGenericPoint (f hZ.1.genericPoint) (closure (Set.image f Z)) :=
    (hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)).image hf
  rw [Set.eq_univ_of_univ_subset hz'] at hgen
  refine ⟨_, hgen.eq (genericPoint_spec Y)⟩


-- created on 2026-10-20
