module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.BoundaryPruningClose.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.BKSpanningTreeClose.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.OpenSpanningForestClose.Part4
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech.Lattice StatMech.ConfigSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SecondPeelingClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

variable {d : ℕ}


def spc_OnBPath {V : Type*} (T : SimpleGraph V) (B : Set V) (v : V) : Prop :=
  ∃ b₁ b₂ : V, b₁ ∈ B ∧ b₂ ∈ B ∧ b₁ ≠ b₂ ∧ ∃ p : T.Walk b₁ b₂, p.IsPath ∧ v ∈ p.support


end Percolation
end StatMech
