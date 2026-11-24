module
public import Theorem.StatisticalMechanics.Code.FK.FreeDLRKernel.Part2
public import Theorem.StatisticalMechanics.Code.FK.InfiniteFiniteEnergy.Part2
public import Theorem.StatisticalMechanics.Code.FK.TrifurcationPatternCapstone
public import Theorem.StatisticalMechanics.Code.Ising.GibbsExtremeClose
public import Theorem.StatisticalMechanics.Code.Probability.InfiniteHarris.Part3
open MeasureTheory Set Topology
open scoped BigOperators ENNReal StatMech


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRExtreme.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

open StatMech.Lattice

open StatMech.Percolation

variable {E : Type*}


def exactFiniteCylinder (F : Finset E) (omega : ConfigSpace E) :
    Set (ConfigSpace E) :=
  {eta | ∀ e ∈ F, eta e = omega e}

end FK
end StatMech
