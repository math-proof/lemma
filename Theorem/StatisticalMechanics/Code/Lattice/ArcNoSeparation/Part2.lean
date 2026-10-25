/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.FiniteComplementConnected
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Def.StatisticalMechanics.Code.Lattice.ArcNoSeparation.Part2
open Set SimpleGraph


namespace StatMech

namespace Lattice

theorem arcns_connected_of_reachesFarLeft {B : Set (Site 2)} (h : arcns_ReachesFarLeft B) :
    arcns_OffSupportConnected B := by
  obtain ⟨b, hb, hreach⟩ := h
  intro x y hx hy
  obtain ⟨zx, px, hpx, hzx⟩ := hreach x hx
  obtain ⟨zy, py, hpy, hzy⟩ := hreach y hy
  obtain ⟨pc, hpc⟩ := arcns_farLeft_connected B b hb zx zy hzx hzy
  
  refine (?_ : (ffc_offSupportLattice B).Reachable x zx).trans
    (((?_ : (ffc_offSupportLattice B).Reachable zx zy).trans
      (?_ : (ffc_offSupportLattice B).Reachable zy y)))
  · exact (ffc_reachable_iff_offSupportWalk hx).mpr ⟨px, hpx⟩
  · exact (ffc_reachable_iff_offSupportWalk
      (by have := hpx zx px.end_mem_support; exact this)).mpr ⟨pc, hpc⟩
  · exact ((ffc_reachable_iff_offSupportWalk hy).mpr ⟨py, hpy⟩).symm


end Lattice
end StatMech
