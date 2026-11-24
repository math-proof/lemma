module
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
public import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
public import Theorem.StatisticalMechanics.Code.Universality.Defs.Part2
open MeasureTheory Set
open scoped ENNReal NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Defs.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim


variable {d : ℕ}


def percolationEvent (d : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | (originCluster d ω).Infinite}

end Universality
end StatMech
