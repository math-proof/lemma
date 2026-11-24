module
public import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.Theta
public import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part3
open MeasureTheory Function Set
open scoped NNReal ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

open StatMech.Lattice


variable {d : ℕ}


def clusterEvent (d : ℕ) (S : Set (Site d)) (o : Site d) (K : Set (Site d)) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | clusterWithin d ω S o = K}


end Percolation
end StatMech
