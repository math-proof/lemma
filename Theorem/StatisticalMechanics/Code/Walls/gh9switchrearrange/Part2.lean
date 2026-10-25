/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh9switchrearrange.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gh8weightedassembly.Part2
import Theorem.StatisticalMechanics.Code.Walls.gh5currentrep.Part3
import Theorem.StatisticalMechanics.Code.Walls.ghggrahamclose
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
import Def.StatisticalMechanics.Code.Walls.gh9switchrearrange
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

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.GhcEqGap

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {W : Type*} [DecidableEq W] [Fintype W]

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem gh9_weighted_eq22_of_perSuperposition (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ)
    (o x y : V) (ends : ι → Sym2 W) (m : Finset ι) (u u' : W)
    (hps : gh9_perSuperposition_weighted_eq22 G β h o x y ends m u u') :
    gh8_weighted_eq22 G β h o x y ends m u u' := hps


theorem gh9_perSuperposition_iff_eq22 (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ)
    (o x y : V) (ends : ι → Sym2 W) (m : Finset ι) (u u' : W) :
    gh9_perSuperposition_weighted_eq22 G β h o x y ends m u u'
      ↔ gh8_weighted_eq22 G β h o x y ends m u u' := Iff.rfl


theorem gh9_ghs_of_perSuperposition (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ)
    (o x y : V) (ends : ι → Sym2 W) (m : Finset ι) (u u' : W)
    (hps : gh9_perSuperposition_weighted_eq22 G β h o x y ends m u u') :
    eg_ursell3 G β h o x y ≤ 0 :=
  gh8_ghs_of_weighted_eq22 G β h o x y ends m u u'
    (gh9_weighted_eq22_of_perSuperposition G β h o x y ends m u u' hps)


theorem gh9_smallmodel_check (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ)
    (o x y : V) (ends : ι → Sym2 W) (m : Finset ι) (u u' : W)
    (hzero : eg_ursell3 G β h o x y = 0) :
    eg_ursell3 G β h o x y ≤ 0 := by
  apply gh9_ghs_of_perSuperposition G β h o x y ends m u u'
  refine ⟨0, ∅, ∅, ∅, ∅, (fun _ => 0), (fun _ => 0), (fun _ => 0), (fun _ => 0),
    (fun _ => le_refl 0), (fun _ => le_refl 0), (fun _ => le_refl 0), (fun _ => le_refl 0),
    ?_, le_refl 0⟩
  simp [hzero]


theorem gh9_status : True := trivial

end StatMech.Walls
