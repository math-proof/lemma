/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMergeGeom
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


def NeighborTrifPrecursor (d : ℕ) (a₁ a₂ a₃ : Site d) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃) ∧
    ((cluster d (removeSite 0 ω) a₁).Infinite ∧ (cluster d (removeSite 0 ω) a₂).Infinite ∧
      (cluster d (removeSite 0 ω) a₃).Infinite) ∧
    (¬ Connected d (removeSite 0 ω) a₁ a₂ ∧ ¬ Connected d (removeSite 0 ω) a₁ a₃ ∧
      ¬ Connected d (removeSite 0 ω) a₂ a₃)}


end Percolation
end StatMech
