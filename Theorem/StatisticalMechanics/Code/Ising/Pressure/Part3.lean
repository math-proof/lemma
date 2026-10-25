/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Pressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Def.StatisticalMechanics.Code.Ising.Pressure.Part3
open scoped BigOperators
open Finset Filter Topology


namespace StatMech

namespace Ising

theorem logZSeq_eq {Ω : Type*} [Fintype Ω] [Nonempty Ω] (β : ℝ) (E : Ω → ℝ) (n : ℕ) :
    logZSeq β E n = n * Real.log (Z β E) := by
  unfold logZSeq
  rw [Zpow_eq, Real.log_pow]


theorem logZSeq_subadditive {Ω : Type*} [Fintype Ω] [Nonempty Ω] (β : ℝ) (E : Ω → ℝ) :
    Subadditive (logZSeq β E) := by
  intro m n
  rw [logZSeq_eq, logZSeq_eq, logZSeq_eq]
  have hcast : ((m + n : ℕ) : ℝ) = (m : ℝ) + n := by push_cast; ring
  rw [hcast]
  apply le_of_eq
  ring


theorem logZSeq_bddBelow {Ω : Type*} [Fintype Ω] [Nonempty Ω] (β : ℝ) (E : Ω → ℝ) :
    BddBelow (Set.range fun n => logZSeq β E n / n) := by
  refine ⟨min 0 (Real.log (Z β E)), ?_⟩
  rintro x ⟨n, rfl⟩
  simp only
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [logZSeq, Zpow, Nat.cast_zero, div_zero]
    exact min_le_left _ _
  · rw [logZSeq_eq, mul_div_cancel_left₀ _ (by exact_mod_cast hn.ne')]
    exact min_le_right _ _


end Ising
end StatMech
