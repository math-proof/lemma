/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part12
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part4
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexCentralQuantumNumber_rev {n : ℕ} (j : Fin n) :
    sixVertexCentralQuantumNumber j.rev =
      -sixVertexCentralQuantumNumber j := by
  simp [sixVertexCentralQuantumNumber]
  ring

theorem sixVertexCentralQuantumNumber_eq {n : ℕ} (j : Fin n) :
    sixVertexCentralQuantumNumber j =
      (j.val : ℝ) - ((n : ℝ) - 1) / 2 := by
  simp [sixVertexCentralQuantumNumber]
  ring

theorem sum_sixVertexCentralQuantumNumber (n : ℕ) :
    ∑ j : Fin n, sixVertexCentralQuantumNumber j = 0 := by
  have hrev : (∑ j : Fin n, (j.rev.val : ℝ)) = ∑ j : Fin n, (j.val : ℝ) := by
    apply Fintype.sum_equiv Fin.revPerm
    intro j
    rfl
  unfold sixVertexCentralQuantumNumber
  rw [← Finset.sum_div, Finset.sum_sub_distrib, hrev, sub_self, zero_div]

theorem strictMono_sixVertexCentralQuantumNumber (n : ℕ) :
    StrictMono (sixVertexCentralQuantumNumber : Fin n → ℝ) := by
  intro j k hjk
  rw [sixVertexCentralQuantumNumber_eq,
    sixVertexCentralQuantumNumber_eq]
  have hval : (j.val : ℝ) < k.val := by exact_mod_cast hjk
  linarith


end
end StatMech.FrontierD
