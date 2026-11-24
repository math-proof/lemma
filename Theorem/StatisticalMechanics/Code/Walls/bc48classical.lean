module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
public import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
public import Theorem.StatisticalMechanics.Code.Walls.bc47trifarms.Part6
public import Theorem.StatisticalMechanics.Code.Walls.bc46funnelproof.Part6
public import Def.StatisticalMechanics.Code.Walls.bc48classical
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
set_option linter.style.longLine false
set_option maxRecDepth 4000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc48_mem_classicalTrifFinset {ω : ConfigSpace (Sym2 (Site d))} {n : ℕ} {x : Site d} :
    x ∈ bc48_classicalTrifFinset ω n ↔ x ∈ box d n ∧ bc47_IsClassicalTrifurcation ω x := by
  classical
  rw [bc48_classicalTrifFinset, Finset.mem_filter, boxFinsetBK, Set.Finite.mem_toFinset]

end StatMech.Walls
