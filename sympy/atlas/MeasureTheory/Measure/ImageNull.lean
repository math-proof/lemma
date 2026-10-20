/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/ImageNull.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Topology.NhdsWithin

/-!
# Images of locally null sets

A set in a second-countable space whose image is locally null has null image.
-/

open MeasureTheory

namespace MathlibExt.MeasureTheory

variable {X Y : Type*} [TopologicalSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y]
variable {μ : Measure Y} {f : X → Y} {s : Set X}

/-- A set whose image is locally null has null image (second-countable domain). -/
theorem measure_image_null_of_locally_null
    (h : ∀ x ∈ s, ∃ V ∈ nhds x, μ (f '' (V ∩ s)) = 0) :
    μ (f '' s) = 0 := by
  have hall : ∀ x : X, ∃ V ∈ nhds x, (x ∈ s → μ (f '' (V ∩ s)) = 0) := by
    intro x
    by_cases hx : x ∈ s
    · obtain ⟨V, hVm, hVn⟩ := h x hx
      exact ⟨V, hVm, fun _ => hVn⟩
    · exact ⟨Set.univ, Filter.univ_mem, fun hcon => absurd hcon hx⟩
  choose V hVmem hVnull using hall
  have hmem : ∀ x ∈ s, V x ∈ nhdsWithin x s := fun x hx =>
    mem_nhdsWithin_of_mem_nhds (hVmem x)
  obtain ⟨T, hTsub, hTcount, hcover⟩ :=
    TopologicalSpace.countable_cover_nhdsWithin hmem
  have hsub : f '' s ⊆ ⋃ x ∈ T, f '' (V x ∩ s) := by
    intro y hy
    obtain ⟨x, hxS, rfl⟩ := hy
    have hxU : x ∈ ⋃ x ∈ T, V x := hcover hxS
    simp only [Set.mem_iUnion] at hxU
    obtain ⟨z, hzT, hzx⟩ := hxU
    simp only [Set.mem_iUnion]
    exact ⟨z, hzT, Set.mem_image_of_mem f ⟨hzx, hxS⟩⟩
  have hnull : μ (⋃ x ∈ T, f '' (V x ∩ s)) = 0 := by
    rw [measure_biUnion_null_iff hTcount]
    intro z hz
    exact hVnull z (hTsub hz)
  exact measure_mono_null hsub hnull

end MathlibExt.MeasureTheory
