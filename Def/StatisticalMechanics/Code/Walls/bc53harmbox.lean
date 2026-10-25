/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc53harmbox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc52jordanbridge.Part2
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Theorem.StatisticalMechanics.Code.Walls.bc53harmbox
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


namespace Bc53Witness

open StatMech.Percolation.CtcWitness


noncomputable def g : Multiplicative (Site 2) := Multiplicative.ofAdd (![(1 : ℤ), 0] : Site 2)


noncomputable def bwallConfig : ConfigSpace (Sym2 (Site 2)) := shift g threeRayConfig


end Bc53Witness
end StatMech.Walls
