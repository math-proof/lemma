/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean -/

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
import Theorem.StatisticalMechanics.Code.Walls.wcbcolumnbridge.Part4
import Theorem.StatisticalMechanics.Code.Walls.wstsigntoggle.Part2
import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part4
import Theorem.StatisticalMechanics.Code.Walls.wisindicatorsteps.Part4
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

open StatMech.Walls


def wis_twoToggle : ℕ → ℤ := fun i => if i = 1 ∨ i = 2 then 1 else 0


end Lattice
end StatMech
