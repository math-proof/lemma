/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SubcriticalDecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
open MeasureTheory Set
open scoped NNReal ENNReal


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


def crossingEvent (d n : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | ∃ v, Connected d ω (origin d) v ∧ v ∉ box d (n - 1)}

end Percolation
end StatMech
