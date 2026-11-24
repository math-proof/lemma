module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
public import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
public import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
public import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
public import Theorem.StatisticalMechanics.Code.Walls.bc38acyclic.Part6
public import Theorem.StatisticalMechanics.Code.Walls.bc39spanning.Part3
public import Theorem.StatisticalMechanics.Code.Walls.bc40funnel.Part4
public import Theorem.StatisticalMechanics.Code.Walls.bc41rootside.Part3
public import Theorem.StatisticalMechanics.Code.Walls.bc42rootward.Part2
public import Theorem.StatisticalMechanics.Code.Walls.bc43rootparent
public import Theorem.StatisticalMechanics.Code.Walls.bc44rootwalk.Part3
public import Def.StatisticalMechanics.Code.Walls.bc45depthwalk
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
set_option linter.style.longLine false
set_option maxRecDepth 4000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc45depthwalk.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc45_idx_injective (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    Function.Injective (bc45_idx ω n) :=
  ((inferInstance : Countable (Site d)).exists_injective_nat).choose_spec

end StatMech.Walls
