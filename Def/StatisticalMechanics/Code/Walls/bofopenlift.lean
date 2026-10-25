/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.benentryleg.Part2
import Theorem.StatisticalMechanics.Code.Walls.bcrboxrep.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc57coarsetrif.Part3
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation


open Classical in


noncomputable def bof_ce : ConfigSpace (Sym2 (Site 2)) :=
  fun e =>
    if ((∃ k : ℤ, e = s(bc57_pt k 0, bc57_pt (k + 1) 0)) ∨
        (∃ k : ℤ, e = s(bc57_pt k 2, bc57_pt (k + 1) 2)) ∨
        (e = s(bc57_pt 0 0, bc57_pt 0 1)) ∨
        (e = s(bc57_pt 0 1, bc57_pt 0 2)))
      then true else false


end StatMech.Walls
