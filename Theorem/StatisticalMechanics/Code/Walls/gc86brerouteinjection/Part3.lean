/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc86brerouteinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc85bthreereplicaswitch.Part3
import Def.StatisticalMechanics.Code.Walls.gc86brerouteinjection.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {W : Type*} [DecidableEq W] [Fintype W]


theorem gc86b_bijection_iff_residual (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    gc85b_ThreeCurrentBijection ends m o x y g ↔ gc86b_CogxgResidual ends m o x y g := by
  unfold gc85b_ThreeCurrentBijection gc86b_CogxgResidual
  constructor
  · intro h; zify at h ⊢; omega
  · intro h; zify; omega


theorem gc86b_bijection_of_residual (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    (hres : gc86b_CogxgResidual ends m o x y g) :
    gc85b_ThreeCurrentBijection ends m o x y g :=
  (gc86b_bijection_iff_residual ends m o x y g).2 hres


end StatMech.Walls
