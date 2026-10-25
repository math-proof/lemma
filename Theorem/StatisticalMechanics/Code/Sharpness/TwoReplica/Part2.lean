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
import Def.StatisticalMechanics.Code.Sharpness.TwoReplica
open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem summable_norm_wEdge (β : ℝ) (J : Sym2 V → ℝ) (e : Sym2 V) :
    Summable (fun k => ‖wEdge β J e k‖) := by
  unfold wEdge
  have h2 : Summable (fun k : ℕ => (|β * J e|) ^ k / k.factorial) := by
    have := NormedSpace.expSeries_summable' (𝕂 := ℝ) (|β * J e|)
    convert this using 2 with k; rw [smul_eq_mul, div_eq_inv_mul]
  refine h2.congr (fun k => ?_)
  rw [Real.norm_eq_abs, abs_div, abs_pow]
  congr 1
  exact (abs_of_nonneg (by positivity)).symm


theorem summable_norm_weight_ofEdgeFun (β : ℝ) (J : Sym2 V → ℝ) :
    Summable (fun m : ↥G.edgeFinset → ℕ => ‖weight G β J (ofEdgeFun G m)‖) := by
  have h := (prod_tsum_fubini (fun (e : Sym2 V) k => ‖wEdge β J e k‖)
    (fun e => summable_norm_wEdge β J e) (fun _ _ => norm_nonneg _) G.edgeFinset).1
  refine h.congr (fun m => ?_)
  rw [weight_ofEdgeFun, norm_prod]
  exact Finset.prod_congr rfl (fun e _ => rfl)


theorem summable_norm_currentSum_summand (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      ‖if sources G (ofEdgeFun G m) = A then weight G β J (ofEdgeFun G m) else 0‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (summable_norm_weight_ofEdgeFun G β J)
  by_cases h : sources G (ofEdgeFun G m) = A <;> simp [h]


end Sharpness
end StatMech
