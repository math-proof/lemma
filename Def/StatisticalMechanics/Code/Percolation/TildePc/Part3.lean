module
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Percolation.Theta
public import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.TildePc.Part2
open MeasureTheory
open scoped NNReal
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TildePc.lean -/
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


def tildePcSet (d : ℕ) : Set NNReal :=
  {p : NNReal | ∃ hp : p ≤ 1, ∃ S : Finset (Site d), origin d ∈ S ∧ phi d p hp S < 1}

end Percolation
end StatMech
