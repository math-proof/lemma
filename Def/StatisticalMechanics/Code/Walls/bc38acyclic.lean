module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
public import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
public import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
public import Theorem.StatisticalMechanics.Code.Percolation.RootedForestPeelClose.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeTrifClose.Part2
public import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
public import Theorem.StatisticalMechanics.Code.Walls.bc35globalarm
public import Theorem.StatisticalMechanics.Code.Walls.bc36rooteddiv.Part2
public import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
public import Theorem.StatisticalMechanics.Code.Walls.bc38acyclic
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech.Lattice StatMech.ConfigSpace
set_option linter.style.longLine false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


open Classical in


noncomputable def bc38_parentTo {V : Type*} (G : SimpleGraph V) (root : V → V) (v : V) : V :=
  if h : v ≠ root v ∧ G.Reachable (root v) v then
    (bc38_exists_closer_neighbour G h.2 h.1).choose
  else v


end StatMech.Walls
