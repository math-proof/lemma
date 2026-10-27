import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MeasureTheory.Measure.ImageNull
open MeasureTheory
open MathlibExt.MeasureTheory


namespace MathlibExt.MeasureTheory

/--
[measure_image_null_of_locally_null](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/ImageNull.lean)
-/
@[path]
lemma measure_image_null_of_locally_null
  [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace Y]
  {μ : Measure Y}
  {f : X → Y}
  {s : Set X}
-- given
  (h : ∀ x ∈ s, ∃ V ∈ nhds x, μ (f '' (V ∩ s)) = 0) :
-- imply
  μ (f '' s) = 0 := by
-- proof
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


-- created on 2026-10-20
-- updated on 2026-10-26
