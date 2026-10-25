/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MultiReplica.lean -/

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
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem weight_mul₃_eq (β : ℝ) (J : Sym2 V → ℝ) (n₁ n₂ n₃ : Current V) :
    weight G β J n₁ * weight G β J n₂ * weight G β J n₃
      = (∏ e ∈ G.edgeFinset,
          ((Nat.choose (n₁ e + n₂ e + n₃ e) (n₁ e) : ℝ)
            * (Nat.choose (n₂ e + n₃ e) (n₂ e) : ℝ)))
        * weight G β J (fun e => n₁ e + n₂ e + n₃ e) := by
  rw [weight_mul_eq G β J n₁ n₂, mul_assoc, weight_mul_eq G β J (fun e => n₁ e + n₂ e) n₃]
  
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  
  
  refine congrArg (· * weight G β J (fun e => n₁ e + n₂ e + n₃ e))
    (Finset.prod_congr rfl (fun e _ => ?_))
  
  rw [← Nat.cast_mul, ← Nat.cast_mul]
  congr 1
  
  set a := n₁ e
  set b := n₂ e
  set c := n₃ e
  
  show (a + b).choose a * (a + b + c).choose (a + b)
      = (a + b + c).choose a * (b + c).choose b
  have hab : (a + b).choose a * a.factorial * b.factorial = (a + b).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
    simpa using h
  have habc1 : (a + b + c).choose (a + b) * (a + b).factorial * c.factorial
      = (a + b + c).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := a + b + c) (k := a + b) (by omega)
    simpa [Nat.add_sub_cancel] using h
  have habc2 : (a + b + c).choose a * a.factorial * (b + c).factorial
      = (a + b + c).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := a + b + c) (k := a) (by omega)
    have he : a + b + c - a = b + c := by omega
    rw [he] at h; exact h
  have hbc : (b + c).choose b * b.factorial * c.factorial = (b + c).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right b c)
    simpa using h
  have e1 : (a + b).choose a * (a + b + c).choose (a + b)
        * (a.factorial * b.factorial * c.factorial) = (a + b + c).factorial := by
    calc (a + b).choose a * (a + b + c).choose (a + b) * (a.factorial * b.factorial * c.factorial)
        = (a + b + c).choose (a + b) * ((a + b).choose a * a.factorial * b.factorial) * c.factorial := by ring
      _ = (a + b + c).choose (a + b) * (a + b).factorial * c.factorial := by rw [hab]
      _ = (a + b + c).factorial := habc1
  have e2 : (a + b + c).choose a * (b + c).choose b
        * (a.factorial * b.factorial * c.factorial) = (a + b + c).factorial := by
    calc (a + b + c).choose a * (b + c).choose b * (a.factorial * b.factorial * c.factorial)
        = (a + b + c).choose a * a.factorial * ((b + c).choose b * b.factorial * c.factorial) := by ring
      _ = (a + b + c).choose a * a.factorial * (b + c).factorial := by rw [hbc]
      _ = (a + b + c).factorial := habc2
  have hpos : 0 < a.factorial * b.factorial * c.factorial := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos (e1.trans e2.symm)


theorem ofEdgeFun_add₃ (p q r : ↥G.edgeFinset → ℕ) :
    (fun e => (ofEdgeFun G p) e + (ofEdgeFun G q) e + (ofEdgeFun G r) e)
      = ofEdgeFun G (fun i => p i + q i + r i) := by
  ext e
  unfold ofEdgeFun
  by_cases h : e ∈ G.edgeFinset <;> simp [h]


theorem sources_add₃ (n₁ n₂ n₃ : Current V) :
    sources G (fun e => n₁ e + n₂ e + n₃ e)
      = sources G n₁ ∆ sources G n₂ ∆ sources G n₃ := by
  have h1 : sources G (fun e => n₁ e + n₂ e + n₃ e)
      = sources G (fun e => (fun e => n₁ e + n₂ e) e + n₃ e) := rfl
  rw [h1, sources_add, sources_add]


theorem sources_ofEdgeFun_add₃ (m K₁ K₂ : ↥G.edgeFinset → ℕ)
    (hK : ∀ e, K₁ e + K₂ e ≤ m e) :
    sources G (ofEdgeFun G m)
      = sources G (ofEdgeFun G K₁) ∆ sources G (ofEdgeFun G K₂)
          ∆ sources G (ofEdgeFun G (fun e => m e - K₁ e - K₂ e)) := by
  have hsplit : ofEdgeFun G m
      = fun e => (ofEdgeFun G K₁) e + (ofEdgeFun G K₂) e
          + (ofEdgeFun G (fun e => m e - K₁ e - K₂ e)) e := by
    rw [ofEdgeFun_add₃]
    congr 1
    ext i
    have := hK i
    omega
  rw [hsplit, sources_add₃]


end Sharpness
end StatMech
