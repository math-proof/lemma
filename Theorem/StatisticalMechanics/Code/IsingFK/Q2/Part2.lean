/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Q2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.Potts.Part6
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.IsingFK.Q2.Part2
open scoped BigOperators


namespace StatMech

namespace IsingFK

open Potts Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem pOfBeta_strictMonoOn : StrictMonoOn pOfBeta (Set.Ici (0 : ℝ)) := by
  intro a _ b _ hab
  unfold pOfBeta
  have : Real.exp (-2 * b) < Real.exp (-2 * a) := Real.exp_lt_exp.mpr (by linarith)
  linarith


theorem pOfBeta_mem_Ico (β : ℝ) (hβ : 0 ≤ β) : pOfBeta β ∈ Set.Ico (0 : ℝ) 1 := by
  unfold pOfBeta
  refine ⟨?_, ?_⟩
  · have : Real.exp (-2 * β) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  · have : 0 < Real.exp (-2 * β) := Real.exp_pos _
    linarith


theorem betaOfP_pOfBeta (β : ℝ) : betaOfP (pOfBeta β) = β := by
  unfold betaOfP pOfBeta
  rw [sub_sub_cancel, Real.log_exp]; ring


theorem pOfBeta_betaOfP (p : ℝ) (hp : p < 1) : pOfBeta (betaOfP p) = p := by
  unfold pOfBeta betaOfP
  have h1 : (0 : ℝ) < 1 - p := by linarith
  rw [show -2 * (-(1 / 2) * Real.log (1 - p)) = Real.log (1 - p) by ring, Real.exp_log h1]
  ring


theorem pOfBeta_bijOn : Set.BijOn pOfBeta (Set.Ici (0 : ℝ)) (Set.Ico (0 : ℝ) 1) := by
  refine ⟨fun β hβ => pOfBeta_mem_Ico β hβ, pOfBeta_strictMonoOn.injOn, ?_⟩
  intro p hp
  refine ⟨betaOfP p, ?_, pOfBeta_betaOfP p hp.2⟩
  
  have h1 : (0 : ℝ) < 1 - p := by have := hp.2; linarith
  have h2 : 1 - p ≤ 1 := by have := hp.1; linarith
  have : Real.log (1 - p) ≤ 0 := Real.log_nonpos h1.le h2
  simp only [Set.mem_Ici, betaOfP]
  linarith

end IsingFK
end StatMech
