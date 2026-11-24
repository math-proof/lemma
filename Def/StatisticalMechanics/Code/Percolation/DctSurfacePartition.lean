module
public import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.DctDifferential.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.LastExit.Part2
open MeasureTheory Function Set SimpleGraph
open scoped NNReal ENNReal
open StatMech


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean -/
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


def pivotalEvent (e : Sym2 (Site d)) (A : Set (ConfigSpace (Sym2 (Site d)))) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | IsPivotal e A ω}

end Percolation
end StatMech
