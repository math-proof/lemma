/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_crosscountparity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Walls.kwd_crosscountparity.Part2
open Finset Set SimpleGraph
open StatMech.Lattice


namespace StatMech.Walls

open Classical in


noncomputable def kwd_crossCountZ2 (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : ℕ :=
  w.edges.countP (fun e => decide (bdEdge S e))

open Classical in


noncomputable def kwd_sideBool (S : Set (Site 2)) : Site 2 → Bool := fun v => decide (v ∈ S)

end StatMech.Walls
