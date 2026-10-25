/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Def.StatisticalMechanics.Code.Lattice.JordanInteriorLib
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

@[simp] theorem jil_mem_offSupportInterior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (z : Site 2) :
    z ∈ jil_offSupportInterior Vc ↔ z ∉ Vc.support ∧ z ∈ jec_leftRegion Vc := Iff.rfl


theorem jil_floodFill_subset_offSupportInterior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support) (hseedIn : seed ∈ jec_leftRegion Vc) :
    ffc_floodFill {p | p ∈ Vc.support} seed ⊆ jil_offSupportInterior Vc := by
  intro z hz
  rw [jil_mem_offSupportInterior]
  refine ⟨?_, jil_floodFill_subset_leftRegion Vc hseed hseedIn hz⟩
  have := ffc_floodFill_offSupport (B := {p | p ∈ Vc.support}) (by
    simpa using hseed) hz
  simpa using this


end Lattice
end StatMech
