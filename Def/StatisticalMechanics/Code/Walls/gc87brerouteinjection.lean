/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc87brerouteinjection.lean -/

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
import Theorem.StatisticalMechanics.Code.Walls.gc86brerouteinjection.Part4
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


noncomputable def gc87b_T3 (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) : ℕ :=
  ∑ J₁ ∈ (m.powerset.filter (fun K => sources ends K = ∅)).filter
      (fun J₁ => connK ends (m \ J₁) o x ∧ connK ends (m \ J₁) o y ∧ connK ends (m \ J₁) o g),
    gc86b_ncount ends (m \ J₁) ∅


def gc87b_slack (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) : ℤ :=
  ((gc85b_pcount ends m ∅ {o, g} : ℤ) + (gc85b_pcount ends m ∅ {o, x} : ℤ)
      + (gc85b_pcount ends m ∅ {o, y} : ℤ)) - (gc85b_pcount ends m ∅ ∅ : ℤ)


end StatMech.Walls
