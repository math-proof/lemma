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
import Def.StatisticalMechanics.Code.Lattice.ArcSides.Part2
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


@[simp] theorem mem_arcS_leftRegion (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) (z : Site 2) :
    z ∈ arcS_leftRegion ω α β m m' c d xB hxB ↔
      z ∈ rect α β c d ∧ (z 0 = α ∨ z ∈ floodFromLeft ω α β m m' c d xB hxB) := Iff.rfl


theorem floodFromLeft_subset (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) {z : Site 2}
    (hz : z ∈ floodFromLeft ω α β m m' c d xB hxB) :
    z ∈ rect α β c d ∧ z ∉ overlapComp ω m m' c d xB hxB := by
  obtain ⟨x, hxbox, _, hxP, w⟩ := hz
  obtain ⟨ww⟩ := w
  exact boxMinusP_walk_dest ω α β m m' c d xB hxB hxbox hxP ww


theorem arcS_leftRegion_subset_box (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) {z : Site 2}
    (hz : z ∈ arcS_leftRegion ω α β m m' c d xB hxB) : z ∈ rect α β c d := hz.1


theorem arcS_leftRegion_left (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d)
    (z : Site 2) (hz : z ∈ rect α β c d) (hzα : z 0 = α) :
    z ∈ arcS_leftRegion ω α β m m' c d xB hxB :=
  ⟨hz, Or.inl hzα⟩


theorem flood_step (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) {w t : Site 2}
    (hwL : w ∈ arcS_leftRegion ω α β m m' c d xB hxB)
    (hwP : w ∉ overlapComp ω m m' c d xB hxB)
    (hadj : (hypercubicLattice 2).Adj w t) (ht : t ∈ rect α β c d)
    (htP : t ∉ overlapComp ω m m' c d xB hxB) :
    t ∈ floodFromLeft ω α β m m' c d xB hxB := by
  obtain ⟨hwbox, hwcase⟩ := hwL
  have hstep : (boxMinusP ω α β m m' c d xB hxB).Adj w t := ⟨hadj, hwbox, ht, hwP, htP⟩
  rcases hwcase with hwα | hwflood
  · exact ⟨w, hwbox, hwα, hwP, Adj.reachable hstep⟩
  · obtain ⟨x, hxbox, hxα, hxP, hreach⟩ := hwflood
    exact ⟨x, hxbox, hxα, hxP, hreach.trans (Adj.reachable hstep)⟩


theorem arcS_leftRegion_bdEdge (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) (u v : Site 2)
    (hu : u ∈ rect α β c d) (hv : v ∈ rect α β c d)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (arcS_leftRegion ω α β m m' c d xB hxB) s(u, v)) :
    u ∈ overlapComp ω m m' c d xB hxB ∨ v ∈ overlapComp ω m m' c d xB hxB := by
  classical
  rw [bdEdge_mk] at hbd
  by_contra hcon
  push Not at hcon
  obtain ⟨huP, hvP⟩ := hcon
  by_cases hvL : v ∈ arcS_leftRegion ω α β m m' c d xB hxB
  · 
    have huL : u ∉ arcS_leftRegion ω α β m m' c d xB hxB := fun h => (hbd.mp h) hvL
    exact huL ⟨hu, Or.inr (flood_step ω α β m m' c d xB hxB hvL hvP hadj.symm hu huP)⟩
  · 
    have huL : u ∈ arcS_leftRegion ω α β m m' c d xB hxB := hbd.mpr hvL
    exact hvL ⟨hv, Or.inr (flood_step ω α β m m' c d xB hxB huL huP hadj hv hvP)⟩


end Lattice
end StatMech
