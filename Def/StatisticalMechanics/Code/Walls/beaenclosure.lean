/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.brpreproute.Part2
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation


open Classical in


noncomputable def bea_ce : ConfigSpace (Sym2 (Site 2)) :=
  fun e =>
    if ((∃ k : ℤ, e = s(bc57_pt k 0, bc57_pt (k + 1) 0)) ∨
        (∃ k : ℤ, e = s(bc57_pt k 1, bc57_pt (k + 1) 1)) ∨
        (∃ k : ℤ, e = s(bc57_pt k (-1), bc57_pt (k + 1) (-1))) ∨
        (e = s(bc57_pt 0 0, bc57_pt 0 1)) ∨
        (e = s(bc57_pt 0 0, bc57_pt 0 (-1))))
      then true else false


end StatMech.Walls
