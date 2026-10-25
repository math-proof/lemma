/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForest
import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Mathlib.GroupTheory.Perm.Fin
import Def.StatisticalMechanics.Code.FrontierA.KacWardCycleAssembly.Part2
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open Matrix

open StatMech.Onsager StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.GeneralUmlaufsatz


theorem kw_det_twoOrientationCycle {E : Type*} [Fintype E]
    [DecidableEq E] [Nonempty E]
    (sigma : Equiv.Perm E) (weight : Bool -> E -> ℂ)
    (hcycle : sigma.IsCycle) (hfree : ∀ i, sigma i ≠ i) :
    (1 - kwTwoOrientationCycleTransition sigma weight).det =
      (1 - ∏ i, weight false i) * (1 - ∏ i, weight true i) := by
  have hone : (1 : Matrix (E × Bool) (E × Bool) ℂ) =
      Matrix.blockDiagonal (fun _ : Bool => (1 : Matrix E E ℂ)) :=
    Matrix.blockDiagonal_one.symm
  rw [hone, kwTwoOrientationCycleTransition, <- Matrix.blockDiagonal_sub,
    Matrix.det_blockDiagonal]
  calc
    _ = ∏ b : Bool, (1 - ∏ i, weight b i) := by
      apply Finset.prod_congr rfl
      intro b _
      simpa using kw_det_one_sub_weightedCycle sigma (weight b) hcycle hfree
    _ = _ := by rw [Fintype.prod_bool]; ring


end StatMech.FrontierA
