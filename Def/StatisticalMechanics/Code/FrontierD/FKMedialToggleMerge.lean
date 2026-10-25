/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialToggleMerge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleExact
import Theorem.StatisticalMechanics.Code.FrontierD.PermSameCycleSplit
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleMerge
open Equiv SimpleGraph


namespace StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

variable {T : EvenTorus}


noncomputable def fkMedialBlackRepresentative
    (T : EvenTorus) (d : FKMedialDart T) : FKMedialBlackDart T := by
  classical
  by_cases hd : fkMedialCheckerColor d = false
  · exact ⟨d, hd⟩
  · refine ⟨fkMedialBondMate T d, ?_⟩
    have hne := fkMedialCheckerColor_bondMate_ne T d
    generalize hc : fkMedialCheckerColor d = c at hd hne
    generalize hb : fkMedialCheckerColor (fkMedialBondMate T d) = b at hne ⊢
    cases c <;> cases b <;> simp_all


end
end StatMech.FrontierD
