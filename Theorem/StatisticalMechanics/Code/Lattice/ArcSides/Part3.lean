/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcSides.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
import Theorem.StatisticalMechanics.Code.Universality.VSeparatesFixed.Part2
import Def.StatisticalMechanics.Code.Lattice.ArcSides.Part3
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem arcS_rightWall_in_L_gives_avoiding_walk (ω : ConfigSpace (Sym2 (Site 2)))
    {α β m m' c d : ℤ} (hαβ : α < β) (xB : Site 2) (hxB : xB ∈ rect m m' c d) {y : Site 2}
    (_hy : y ∈ rect α β c d) (hyβ : y 0 = β)
    (hyL : y ∈ arcS_leftRegion ω α β m m' c d xB hxB) :
    ∃ (x : Site 2) (γ : (hypercubicLattice 2).Walk x y),
      x ∈ rect α β c d ∧ x 0 = α ∧
      (∀ z ∈ γ.support, z ∈ rect α β c d ∧ z ∉ overlapComp ω m m' c d xB hxB) := by
  classical
  obtain ⟨_, hcase⟩ := hyL
  rcases hcase with hyα | hyflood
  · 
    
    exact absurd (hyα.symm.trans hyβ) (ne_of_lt hαβ)
  · obtain ⟨x, hxbox, hxα, hxP, hreach⟩ := hyflood
    obtain ⟨γ⟩ := hreach
    
    set f := SimpleGraph.Hom.ofLE (boxMinusP_le ω α β m m' c d xB hxB) with hf
    refine ⟨x, γ.map f, hxbox, hxα, ?_⟩
    intro z hz
    have hsupp := SimpleGraph.Walk.support_map f γ
    obtain ⟨z', hz'mem, hz'eq⟩ := List.mem_map.mp (hsupp ▸ hz)
    have hz'fact : z' ∈ rect α β c d ∧ z' ∉ overlapComp ω m m' c d xB hxB :=
      boxMinusP_walk_dest ω α β m m' c d xB hxB hxbox hxP (γ.takeUntil z' hz'mem)
    
    have hzz' : z = z' := by simpa [hf] using hz'eq.symm
    rw [hzz']; exact hz'fact


theorem arcS_leftRegion_right (ω : ConfigSpace (Sym2 (Site 2))) {α β m m' c d : ℤ}
    (hαβ : α < β) (hαm : α ≤ m) (hmm' : m ≤ m') (hm'β : m' ≤ β)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d)
    (hcross : ArcS_TwoPathsCross ω α β m m' c d xB hxB) (z : Site 2)
    (hz : z ∈ rect α β c d) (hzβ : z 0 = β) :
    z ∉ arcS_leftRegion ω α β m m' c d xB hxB := by
  classical
  intro hzL
  obtain ⟨x, γ, hxbox, hxα, hsupp⟩ :=
    arcS_rightWall_in_L_gives_avoiding_walk ω hαβ xB hxB hz hzβ hzL
  obtain ⟨w, hwsupp, hwP⟩ :=
    hcross hαm hmm' hm'β x z hxbox hz hxα hzβ γ (fun z hz => (hsupp z hz).1)
  exact (hsupp w hwsupp).2 hwP


theorem arcS_arc_sides_of_cross (ω : ConfigSpace (Sym2 (Site 2))) {α β m m' c d : ℤ}
    (hαβ : α < β)
    (hcross : ∀ (xB : Site 2) (hxB : xB ∈ rect m m' c d),
      ArcS_TwoPathsCross ω α β m m' c d xB hxB) :
    StatMech.Universality.vsFix_arc_sides ω α β m m' c d := by
  intro hαm hmm' hm'β xB hxB _hxBbot yT _hyT _hcV
  refine ⟨arcS_leftRegion ω α β m m' c d xB hxB, ?_, ?_, ?_⟩
  · intro z hzbox hzα
    exact arcS_leftRegion_left ω α β m m' c d xB hxB z hzbox hzα
  · intro z hzbox hzβ
    exact arcS_leftRegion_right ω hαβ hαm hmm' hm'β xB hxB (hcross xB hxB) z hzbox hzβ
  · intro u v hu hv hadj hbd
    exact arcS_leftRegion_bdEdge ω α β m m' c d xB hxB u v hu hv hadj hbd

end Lattice
end StatMech
