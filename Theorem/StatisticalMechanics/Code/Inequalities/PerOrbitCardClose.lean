/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose.Part3
import Def.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


omit [Fintype α] [DecidableEq α] in


theorem poc_snd_eq (p : ConfigSpace α × ConfigSpace α) (k : ConfigSpace α × ConfigSpace α)
    (hk : orbitKey p = k) : p.2 = poc_keyFlip k p.1 := by
  funext a
  have hor := congrFun (congrArg Prod.fst hk) a
  have hand := congrFun (congrArg Prod.snd hk) a
  simp only [orbitKey] at hor hand
  simp only [poc_keyFlip, poc_flip, ← hor, ← hand]
  revert hor hand
  cases hp1 : p.1 a <;> cases hp2 : p.2 a <;> simp_all


end StatMech
