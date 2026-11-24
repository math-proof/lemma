module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
public import Theorem.StatisticalMechanics.Code.Lattice.ClusterContourBijection.Part4
public import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
public import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
public import Theorem.StatisticalMechanics.Code.IsingFK.MagnetizationCorrespondence
public import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace IsingFK

open StatMech.Ising StatMech.FK StatMech.Lattice StatMech.Percolation

variable {d n : ℕ}


def fToB (a : Fin 2) : Bool := a = 0

end IsingFK
end StatMech
