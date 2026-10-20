import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_IsClosedImmersion_isIso_stalkMap_of_mem_interior_range](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_isIso_stalkMap_of_mem_interior_range.lean)
-/
@[path]
private lemma main
  {C X : (Scheme : Type (u + 1))} (i : C ⟶ X) [IsClosedImmersion i] [IsReduced X]
  (c : C) (hc : i c ∈ interior (Set.range i)) :
  IsIso (i.stalkMap c) := by
  classical
  have hsurj : Function.Surjective (i.stalkMap c) := i.stalkMap_surjective c
  suffices hinj : Function.Injective (i.stalkMap c) from
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  rw [injective_iff_map_eq_zero]
  intro g hg
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq g
  rw [Scheme.Hom.germ_stalkMap_apply] at hg
  obtain ⟨W', hcW', ιU, ιV, hW'⟩ := TopCat.Presheaf.germ_eq C.presheaf
    (U := (TopologicalSpace.Opens.map i.base).obj U) (V := (TopologicalSpace.Opens.map i.base).obj U)
    c hxU hxU (i.app U s) 0 (by rw [hg, map_zero])
  rw [map_zero] at hW'
  obtain ⟨W₀, hW₀open, hW₀⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp W'.2
  let V : X.Opens := U ⊓ ⟨W₀, hW₀open⟩ ⊓ ⟨interior (Set.range i), isOpen_interior⟩
  have hcW0 : i c ∈ W₀ := by
    rw [← Set.mem_preimage, show (i ⁻¹' W₀) = (W' : Set C) from hW₀]
    apply hcW'
  have hcV : i c ∈ V := ⟨⟨hxU, hcW0⟩, hc⟩
  have hVU : V ≤ U := inf_le_left.trans inf_le_left
  have hsV : X.presheaf.map (homOfLE hVU).op s = 0 := by
    apply eq_zero_of_basicOpen_eq_bot
    rw [eq_bot_iff]
    intro y hy
    rw [Scheme.mem_basicOpen''] at hy
    obtain ⟨hyV, hunit⟩ := hy
    exfalso
    obtain ⟨c', rfl⟩ : y ∈ Set.range i := interior_subset hyV.2
    have hc'W' : c' ∈ W' := by
      have h' : c' ∈ i ⁻¹' W₀ := hyV.1.2
      rwa [hW₀] at h'
    have h0 : i.stalkMap c' (X.presheaf.germ U (i c') hyV.1.1 s) = 0 := by
      rw [Scheme.Hom.germ_stalkMap_apply]
      have := TopCat.Presheaf.germ_res_apply C.presheaf ιU c' hc'W' (i.app U s)
      rw [← this, hW', map_zero]
    have hu : IsUnit (i.stalkMap c' (X.presheaf.germ U (i c') hyV.1.1 s)) := by
      rw [TopCat.Presheaf.germ_res_apply] at hunit
      exact hunit.map _
    rw [h0] at hu
    apply not_isUnit_zero hu
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) (i c) hcV s, hsV, map_zero]


-- created on 2026-10-20
