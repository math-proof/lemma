/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wstsigntoggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.umffullrev.Part2
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
import Theorem.StatisticalMechanics.Code.Walls.wnaalternate.Part3
import Theorem.StatisticalMechanics.Code.Walls.wstsigntoggle
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

def wst_IndicatorSteps (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : Prop :=
  ∃ (M : List ℤ) (ind : ℕ → ℤ),
    M.Perm (wnu_signedList z w) ∧
    (∀ e ∈ M, e = 1 ∨ e = -1) ∧ ind 0 = 0 ∧
    ((∀ n, ind n = 0 ∨ ind n = 1) ∨ (∀ n, ind n = 0 ∨ ind n = -1)) ∧
    M = (List.range M.length).map (fun i => ind (i + 1) - ind i)


end Lattice
end StatMech
