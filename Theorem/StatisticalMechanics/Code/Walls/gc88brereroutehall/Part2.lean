/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc88brereroutehall.lean -/

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
import Theorem.StatisticalMechanics.Code.Walls.gc87brerouteinjection.Part3
import Def.StatisticalMechanics.Code.Walls.gc88brereroutehall.Part2
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


theorem gc88b_reroute_total (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    {KK JJ : Finset ι × Finset ι} (hKK : KK ∈ gc88b_cogxgSet ends m o x y g)
    (hJJ : JJ ∈ gc88b_T3Set ends m o x y g) :
    gc88b_reroute ends o g KK JJ := by
  simp only [gc88b_cogxgSet, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hKK
  simp only [gc88b_T3Set, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hJJ
  have hK₁ : sources ends KK.1 = ({o, g} : Finset W) := hKK.2.2.1
  have hJ₁ : sources ends JJ.1 = (∅ : Finset W) := hJJ.2.2.1
  unfold gc88b_reroute
  rw [sources_symmDiff, hK₁, hJ₁, show (∅ : Finset W) = ⊥ from rfl, symmDiff_bot]


end StatMech.Walls
