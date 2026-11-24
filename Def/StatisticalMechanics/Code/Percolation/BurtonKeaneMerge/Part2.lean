module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Percolation.BKUniqueness2
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

variable {d : ℕ}


def anchorSites (F : Finset (Sym2 (Site d))) : Set (Site d) :=
  {a | ∃ e ∈ F, a ∈ e}


end Percolation
end StatMech
