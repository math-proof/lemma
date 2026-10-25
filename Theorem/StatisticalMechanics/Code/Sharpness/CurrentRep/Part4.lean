/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Def.StatisticalMechanics.Code.Sharpness.CurrentRep.Part3
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000


namespace StatMech

namespace Sharpness

open StatMech.Ising


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem boltzmannJ_eq_tsum (β : ℝ) (J : Sym2 V → ℝ) (s : ConfigSpace V) :
    boltzmannJ G β J s
      = ∑' m : ↥G.edgeFinset → ℕ,
          weight G β J (ofEdgeFun G m) * ∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e) := by
  
  have hprod : boltzmannJ G β J s = ∏ e ∈ G.edgeFinset, ∑' k, gEdge β J s e k := by
    unfold boltzmannJ
    rw [show (β * ∑ e ∈ G.edgeFinset, J e * bond s e)
          = ∑ e ∈ G.edgeFinset, β * (J e * bond s e) by rw [Finset.mul_sum]]
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl (fun e _ => by rw [tsum_gEdge]; congr 1; ring)
  rw [hprod,
    signed_prod_tsum_fubini (gEdge β J s)
      (fun e => summable_gEdge β J s e) (fun e => summable_norm_gEdge β J s e) G.edgeFinset]
  exact tsum_congr (fun m => prod_gEdge G β J s m)


theorem summable_weight_bond (β : ℝ) (J : Sym2 V → ℝ) (s : ConfigSpace V) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      weight G β J (ofEdgeFun G m) * ∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e)) := by
  have h := summable_prod_signed (gEdge β J s) (fun e => summable_norm_gEdge β J s e) G.edgeFinset
  exact h.congr (fun m => prod_gEdge G β J s m)


theorem spinSum_eq_currentSum (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    (∑ s : ConfigSpace V, spinProd A s * boltzmannJ G β J s)
      = (2 : ℝ) ^ (Fintype.card V) * currentSum G β J A := by
  classical
  
  have hstep1 : ∀ s : ConfigSpace V,
      spinProd A s * boltzmannJ G β J s
        = ∑' m : ↥G.edgeFinset → ℕ,
            weight G β J (ofEdgeFun G m)
              * (spinProd A s * ∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e)) := by
    intro s
    rw [boltzmannJ_eq_tsum, ← tsum_mul_left]
    refine tsum_congr (fun m => ?_); ring
  simp_rw [hstep1]
  
  rw [← Summable.tsum_finsetSum (s := (Finset.univ : Finset (ConfigSpace V)))
    (f := fun s (m : ↥G.edgeFinset → ℕ) =>
      weight G β J (ofEdgeFun G m)
        * (spinProd A s * ∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e)))
    (fun s _ => by
      have h := (summable_weight_bond G β J s).mul_left (spinProd A s)
      refine h.congr (fun m => ?_)
      ring)]
  
  have hinner : ∀ m : ↥G.edgeFinset → ℕ,
      (∑ s : ConfigSpace V,
          weight G β J (ofEdgeFun G m)
            * (spinProd A s * ∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e)))
        = if sources G (ofEdgeFun G m) = A
            then weight G β J (ofEdgeFun G m) * (2 : ℝ) ^ (Fintype.card V) else 0 := by
    intro m
    rw [← Finset.mul_sum]
    have hspin : (∑ s : ConfigSpace V,
          spinProd A s * ∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e))
        = if sources G (ofEdgeFun G m) = A then (2 : ℝ) ^ (Fintype.card V) else 0 := by
      have hbond : ∀ s : ConfigSpace V,
          (∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e))
            = ∏ e ∈ G.edgeFinset, (bond s e) ^ ((ofEdgeFun G m) e) :=
        fun s => (prod_bond_pow_ofEdgeFun G s m).symm
      simp_rw [hbond]
      exact spinSum_monomial_eq G A (ofEdgeFun G m)
    rw [hspin]
    by_cases h : sources G (ofEdgeFun G m) = A <;> simp [h]
  simp_rw [hinner]
  
  unfold currentSum
  rw [mul_comm ((2 : ℝ) ^ (Fintype.card V)), ← tsum_mul_right]
  refine tsum_congr (fun m => ?_)
  by_cases h : sources G (ofEdgeFun G m) = A <;> simp [h]


end Sharpness
end StatMech
