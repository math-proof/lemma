/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplicaWeighted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem weight_reflect_split_eq (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (P : Finset (Sym2 V))
    {K : Current V} (hK : ∀ e, K e ≤ m e) :
    Sharpness.weight G β J (reflect m P K)
        * Sharpness.weight G β J (fun e => m e - reflect m P K e)
      = Sharpness.weight G β J K * Sharpness.weight G β J (fun e => m e - K e) := by
  have hcompl_K : (fun e => K e + (m e - K e)) = m := by
    funext e; exact Nat.add_sub_cancel' (hK e)
  have hRle := reflect_le m P hK
  have hcompl_R : (fun e => reflect m P K e + (m e - reflect m P K e)) = m := by
    funext e; exact Nat.add_sub_cancel' (hRle e)
  rw [Sharpness.weight_mul_eq G β J (reflect m P K) (fun e => m e - reflect m P K e),
      Sharpness.weight_mul_eq G β J K (fun e => m e - K e), hcompl_R, hcompl_K]
  congr 1
  refine Finset.prod_congr rfl (fun e _ => ?_)
  congr 1
  have hr : reflect m P K e + (m e - reflect m P K e) = m e := Nat.add_sub_cancel' (hRle e)
  have hk : K e + (m e - K e) = m e := Nat.add_sub_cancel' (hK e)
  rw [hr, hk]
  unfold reflect
  by_cases h : e ∈ P
  · simp only [if_pos h]; rw [Nat.choose_symm (hK e)]
  · simp only [if_neg h]


end Ising
end StatMech
