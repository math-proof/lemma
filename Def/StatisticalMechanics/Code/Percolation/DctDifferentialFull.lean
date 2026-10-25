/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferentialFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
open MeasureTheory Function Set
open scoped NNReal ENNReal
open StatMech
open Finset


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


def withinConnEvent (d : ℕ) (S : Set (Site d)) (o x : Site d) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | ∃ (ho : o ∈ S) (hx : x ∈ S), ConnectedWithin d ω S ⟨o, ho⟩ ⟨x, hx⟩}

end Percolation
end StatMech
