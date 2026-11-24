module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
public import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
public import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
public import Def.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part2
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

theorem jil_offSupportInterior_subset_floodFill {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hlink : jil_RowLinked Vc seed) :
    jil_offSupportInterior Vc ⊆ ffc_floodFill {p | p ∈ Vc.support} seed := by
  intro z hz
  obtain ⟨p, hp⟩ := hlink z hz
  
  have hzB : z ∉ ({p | p ∈ Vc.support} : Set (Site 2)) := by
    simpa using (jil_mem_offSupportInterior Vc z |>.mp hz).1
  have hreach : (ffc_offSupportLattice {p | p ∈ Vc.support}).Reachable z seed :=
    (ffc_reachable_iff_offSupportWalk hzB).mpr ⟨p, by intro w hw; simpa using hp w hw⟩
  exact hreach.symm


theorem jil_offSupportInterior_eq_floodFill {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support) (hseedIn : seed ∈ jec_leftRegion Vc)
    (hlink : jil_RowLinked Vc seed) :
    jil_offSupportInterior Vc = ffc_floodFill {p | p ∈ Vc.support} seed :=
  Set.Subset.antisymm (jil_offSupportInterior_subset_floodFill Vc hlink)
    (jil_floodFill_subset_offSupportInterior Vc hseed hseedIn)


end Lattice
end StatMech
