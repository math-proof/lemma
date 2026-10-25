/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideReachesClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OutsideConnected.Part4
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


theorem orc_offSupportLattice_reachable_of_offSupport (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hx : x ∉ Vc.support) (h : (offSupport Vc).Reachable x y) :
    (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y := by
  obtain ⟨p, hp⟩ := offSupport_reachable_to_offSupportWalk Vc h hx
  exact (oc_offSupportLattice_reachable_iff Vc hx).mpr ⟨p, hp⟩


theorem orc_offSupport_reachable_of_offSupportLattice (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hx : x ∉ Vc.support)
    (h : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y) :
    (offSupport Vc).Reachable x y := by
  obtain ⟨p, hp⟩ := (oc_offSupportLattice_reachable_iff Vc hx).mp h
  exact offSupportWalk_to_offSupport_reachable Vc p hp


end Lattice
end StatMech
