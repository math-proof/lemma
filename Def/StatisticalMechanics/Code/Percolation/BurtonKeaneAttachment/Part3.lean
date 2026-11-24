module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Percolation.CorridorConfinement.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneAttachment.Part3
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

open DisjointPaths

variable {d : ℕ}


def bka_CorridorConfinement (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  DisjointCorridorRouting ω


end Percolation
end StatMech
