/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferentialFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
import Def.StatisticalMechanics.Code.Percolation.DctDifferentialFull
open MeasureTheory Function Set
open scoped NNReal ENNReal
open StatMech
open Finset


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


@[simp]
theorem mem_withinConnEvent {S : Set (Site d)} {o x : Site d}
    {ω : ConfigSpace (Sym2 (Site d))} :
    ω ∈ withinConnEvent d S o x ↔
      ∃ (ho : o ∈ S) (hx : x ∈ S), ConnectedWithin d ω S ⟨o, ho⟩ ⟨x, hx⟩ :=
  Iff.rfl


end Percolation
end StatMech
