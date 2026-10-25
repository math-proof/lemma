/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TwoReplica.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsing.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem weight_mul_eq (β : ℝ) (J : Sym2 V → ℝ) (n₁ n₂ : Current V) :
    weight G β J n₁ * weight G β J n₂
      = (∏ e ∈ G.edgeFinset, (Nat.choose (n₁ e + n₂ e) (n₁ e) : ℝ))
        * weight G β J (fun e => n₁ e + n₂ e) := by
  unfold weight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  set X := β * J e with hX
  set a := n₁ e
  set b := n₂ e
  have hnat : (a + b).choose a * (a.factorial * b.factorial) = (a + b).factorial := by
    have h := Nat.add_choose_mul_factorial_mul_factorial b a
    rw [Nat.add_comm b a] at h
    rw [← h]; ring
  have hfac : ((a + b).choose a : ℝ) * (a.factorial * b.factorial) = (a + b).factorial := by
    exact_mod_cast hnat
  have haf : (a.factorial : ℝ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
  have hbf : (b.factorial : ℝ) ≠ 0 := by exact_mod_cast b.factorial_ne_zero
  have habf : ((a + b).factorial : ℝ) ≠ 0 := by exact_mod_cast (a + b).factorial_ne_zero
  rw [pow_add]
  field_simp
  rw [← hfac]
  ring


theorem ofEdgeFun_add (p q : ↥G.edgeFinset → ℕ) :
    (fun e => (ofEdgeFun G p) e + (ofEdgeFun G q) e) = ofEdgeFun G (fun i => p i + q i) := by
  ext e
  unfold ofEdgeFun
  by_cases h : e ∈ G.edgeFinset <;> simp [h]


theorem sources_ofEdgeFun_add (m K : ↥G.edgeFinset → ℕ) (hK : K ≤ m) :
    sources G (ofEdgeFun G m)
      = sources G (ofEdgeFun G K) ∆ sources G (ofEdgeFun G (fun e => m e - K e)) := by
  have hsplit : ofEdgeFun G m
      = fun e => (ofEdgeFun G K) e + (ofEdgeFun G (fun e => m e - K e)) e := by
    rw [ofEdgeFun_add]
    congr 1
    ext i
    exact (Nat.add_sub_cancel' (hK i)).symm
  rw [hsplit, sources_add]


end Sharpness
end StatMech
