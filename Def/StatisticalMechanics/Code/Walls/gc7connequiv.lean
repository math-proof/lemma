/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7connequiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc6_pairingpath
import Theorem.StatisticalMechanics.Code.Walls.gc7connequiv
open Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.Walls

open StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent

open StatMech.Sharpness.FluxEdgeCopy

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


def gc7_connSetoid (ends : ι → Sym2 V) (K : Finset ι) : Setoid V :=
  Setoid.mk (connK ends K) (gc7_connK_equivalence ends K)

end StatMech.Walls
