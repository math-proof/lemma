/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMergeGeom
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Def.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem tfc_Tcount_le_boundary_of_residue (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : tfc_BoundaryArmInjection ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n := by
  obtain ⟨φ, hmaps, hinj⟩ := h
  exact tfc_Tcount_le_of_injOn ω n φ hmaps hinj


theorem tfc_Tcount_le_boundary_of_injection
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), tfc_BoundaryArmInjection ω n) :
    ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ),
      Tcount d ω n ≤ boxSV_boundaryCard d n :=
  fun ω n => tfc_Tcount_le_boundary_of_residue ω n (hres ω n)


end Percolation
end StatMech
