module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Percolation.BKUniqueness2
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part2
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


def MergeWitness (d : ℕ) (F : Finset (Sym2 (Site d))) (k : ℕ∞) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | numInfiniteClusters d ω = k ∧
    ∃ x y : Site d, (cluster d ω x).Infinite ∧ (cluster d ω y).Infinite ∧
      cluster d ω x ≠ cluster d ω y ∧ Connected d (forceOpenFinset F ω) x y}


end Percolation
end StatMech
