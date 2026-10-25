/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsHoleFreeBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.TreeNoSepEuler.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable


noncomputable def phb_doubleDualIso (K : Set (Site 2)) :
    latticeMinusBarrier K ≃g whb_faceRegion (faceBoundaryGraph K) where
  toEquiv := phb_doubleDualEquiv
  map_rel_iff' := by
    intro x y
    change (whb_faceRegion (faceBoundaryGraph K)).Adj
        (phb_doubleDualShift x) (phb_doubleDualShift y) ↔
      (latticeMinusBarrier K).Adj x y
    rw [latticeMinusBarrier_adj, whb_faceRegion_adj]
    have hadj := phb_doubleDualShift_latAdj (x := x) (y := y)
    constructor
    · rintro ⟨hshift, hmem⟩
      have hxy := hadj.mp hshift
      refine ⟨hxy, ?_⟩
      rw [← phb_flankFaces_mem_faceBoundaryGraph_iff hxy,
        ← phb_sharedPrimalEdge_shift_eq_flankFaces hxy]
      exact hmem
    · rintro ⟨hxy, hbd⟩
      refine ⟨hadj.mpr hxy, ?_⟩
      rw [phb_sharedPrimalEdge_shift_eq_flankFaces hxy,
        phb_flankFaces_mem_faceBoundaryGraph_iff hxy]
      exact hbd

end Lattice
end StatMech
