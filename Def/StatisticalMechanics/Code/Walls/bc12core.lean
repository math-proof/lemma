module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Walls.bc9core
public import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
public import Theorem.StatisticalMechanics.Code.Walls.bc12core
open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation
open MeasureTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc12core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

variable {d : ℕ}


def bc12_BoxOriginTrifurcation (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, IsCanonicalTrifurcation d ω 0


end Walls
end StatMech
