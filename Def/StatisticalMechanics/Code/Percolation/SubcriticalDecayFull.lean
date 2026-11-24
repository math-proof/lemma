module
public import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecay.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
public import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
public import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull
open MeasureTheory Set
open scoped NNReal ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecayFull.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

open StatMech.Lattice StatMech.ConfigSpace


variable {d : ℕ}


def crossingEventFrom (d : ℕ) (y : Site d) (n : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | ∃ v, Connected d ω y v ∧ v ∉ box d (n - 1)}

end Percolation
end StatMech
