module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMergeGeom
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
public import Def.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part4
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech.Lattice StatMech.ConfigSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem tfc_boundaryArmInjection_of_distinctArmEnds (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : tfc_DistinctArmEnds ω n) : tfc_BoundaryArmInjection ω n := by
  obtain ⟨φ, hmaps, hinj⟩ := h
  exact ⟨φ, fun x hx htri => (hmaps x hx htri).1, hinj⟩


theorem tfc_Tcount_le_boundary_of_distinctArmEnds (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : tfc_DistinctArmEnds ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  tfc_Tcount_le_boundary_of_residue ω n (tfc_boundaryArmInjection_of_distinctArmEnds ω n h)


end Percolation
end StatMech
