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
import Def.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem sourcePairSum_eq_mul (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) :
    sourcePairSum G β J A B = currentSum G β J A * currentSum G β J B := by
  set f : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => if sources G (ofEdgeFun G p) = A then weight G β J (ofEdgeFun G p) else 0 with hf
  set g : (↥G.edgeFinset → ℕ) → ℝ :=
    fun q => if sources G (ofEdgeFun G q) = B then weight G β J (ofEdgeFun G q) else 0 with hg
  have hsumf : Summable f := (summable_norm_currentSum_summand G β J A).of_norm
  have hsumg : Summable g := (summable_norm_currentSum_summand G β J B).of_norm
  have hfg : Summable (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) => f z.1 * g z.2) :=
    summable_mul_of_summable_norm
      (summable_norm_currentSum_summand G β J A) (summable_norm_currentSum_summand G β J B)
  show (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ), f pq.1 * g pq.2)
      = (∑' p, f p) * (∑' q, g q)
  rw [Summable.tsum_mul_tsum hsumf hsumg hfg]


theorem sourcePairSum_eq_superposition (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) :
    sourcePairSum G β J A B
      = ∑' m : ↥G.edgeFinset → ℕ,
          ∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m},
            (if sources G (ofEdgeFun G K.1) = A then weight G β J (ofEdgeFun G K.1) else 0)
              * (if sources G (ofEdgeFun G (fun e => m e - K.1 e)) = B
                    then weight G β J (ofEdgeFun G (fun e => m e - K.1 e)) else 0) := by
  set f : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => if sources G (ofEdgeFun G p) = A then weight G β J (ofEdgeFun G p) else 0 with hf
  set g : (↥G.edgeFinset → ℕ) → ℝ :=
    fun q => if sources G (ofEdgeFun G q) = B then weight G β J (ofEdgeFun G q) else 0 with hg
  have hfg : Summable (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) => f z.1 * g z.2) :=
    summable_mul_of_summable_norm
      (summable_norm_currentSum_summand G β J A) (summable_norm_currentSum_summand G β J B)
  
  set F : (Σ m : (↥G.edgeFinset → ℕ), {p : ↥G.edgeFinset → ℕ // p ≤ m}) → ℝ :=
    fun s => f s.2.1 * g (fun e => s.1 e - s.2.1 e) with hF
  
  have hcomp : ∀ z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
      f z.1 * g z.2 = F (pairEquivSigma z) := by
    rintro ⟨p, q⟩
    simp only [hF, pairEquivSigma, Equiv.coe_fn_mk]
    have hsub : (fun e => (p e + q e) - p e) = q := by ext e; simp
    rw [hsub]
  
  have hsumF : Summable F := by
    rw [← (pairEquivSigma
      (E := ↥G.edgeFinset)).summable_iff]
    exact hfg.congr (fun z => hcomp z)
  
  unfold sourcePairSum
  rw [show (fun pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
        (if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0)
          * (if sources G (ofEdgeFun G pq.2) = B then weight G β J (ofEdgeFun G pq.2) else 0))
      = fun pq => f pq.1 * g pq.2 from rfl]
  rw [tsum_congr hcomp, (pairEquivSigma (E := ↥G.edgeFinset)).tsum_eq F,
    Summable.tsum_sigma hsumF]
  refine tsum_congr (fun m => ?_)
  rw [tsum_fintype]


theorem sourcePairSum_superposition_source (m K : ↥G.edgeFinset → ℕ) (hK : K ≤ m)
    {A B : Finset V} (hA : sources G (ofEdgeFun G K) = A)
    (hB : sources G (ofEdgeFun G (fun e => m e - K e)) = B) :
    sources G (ofEdgeFun G m) = A ∆ B := by
  rw [sources_ofEdgeFun_add G m K hK, hA, hB]


theorem weight_split_eq_binom (β : ℝ) (J : Sym2 V → ℝ)
    (m K : ↥G.edgeFinset → ℕ) (hK : K ≤ m) :
    weight G β J (ofEdgeFun G K) * weight G β J (ofEdgeFun G (fun e => m e - K e))
      = (∏ e ∈ G.edgeFinset,
          (Nat.choose ((ofEdgeFun G m) e) ((ofEdgeFun G K) e) : ℝ))
        * weight G β J (ofEdgeFun G m) := by
  have hsplit : ofEdgeFun G m
      = fun e => (ofEdgeFun G K) e + (ofEdgeFun G (fun e => m e - K e)) e := by
    rw [ofEdgeFun_add]
    congr 1
    ext i
    exact (Nat.add_sub_cancel' (hK i)).symm
  rw [weight_mul_eq G β J (ofEdgeFun G K) (ofEdgeFun G (fun e => m e - K e))]
  congr 1
  · refine Finset.prod_congr rfl (fun e he => ?_)
    have : (ofEdgeFun G m) e
        = (ofEdgeFun G K) e + (ofEdgeFun G (fun e => m e - K e)) e := by rw [hsplit]
    rw [this]
  · rw [← hsplit]

end Sharpness
end StatMech
