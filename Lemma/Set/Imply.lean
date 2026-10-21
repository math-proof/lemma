import Mathlib
import sympy.Basic
open TopologicalSpace
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma isClosed_of_stable
  {X : Type u} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]
  {s : Set X}
  -- given
  (h₀ : StableUnderSpecialization s)
  (h₁ : StableUnderGeneralization s) :
  -- imply
  IsClosed s := by
  -- proof
  have key : ∀ C ∈ irreducibleComponents X, (C ∩ s).Nonempty → C ⊆ s := by
    intro C hC hCs z hz
    obtain ⟨y, hyC, hys⟩ := hCs
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
    apply h₀ (hξ.specializes hz) (h₁ (hξ.specializes hyC) hys)
  have hs : s = ⋃ C ∈ {C ∈ irreducibleComponents X | (C ∩ s).Nonempty}, C := by
    apply le_antisymm
    ·
      intro x hx
      refine Set.mem_biUnion (x := irreducibleComponent x) ⟨irreducibleComponent_mem_irreducibleComponents x,
        ⟨x, mem_irreducibleComponent, hx⟩⟩ mem_irreducibleComponent
    ·
      intro x hx
      obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hx
      apply key C hC.1 hC.2 hxC
  rw [hs]
  apply (NoetherianSpace.finite_irreducibleComponents.subset (fun C hC => hC.1)).isClosed_biUnion
    fun C hC => isClosed_of_mem_irreducibleComponents C hC.1

/--
[TopologicalSpace_NoetherianSpace_isClopen_of_stableUnderSpecialization_of_stableUnderGeneralization](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_TopologicalSpace_NoetherianSpace_isClopen_of_stableUnderSpecialization_of_stableUnderGeneralization.lean)
-/
@[path]
private lemma main
  {X : Type u} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]
  {s : Set X}
  -- given
  (h₀ : StableUnderSpecialization s)
  (h₁ : StableUnderGeneralization s) :
  -- imply
  IsClopen s := by
  -- proof
  refine ⟨isClosed_of_stable h₀ h₁, ?_⟩
  have this := isClosed_of_stable (s := sᶜ) h₁.compl h₀.compl
  rwa [isClosed_compl_iff] at this


-- created on 2026-10-20
