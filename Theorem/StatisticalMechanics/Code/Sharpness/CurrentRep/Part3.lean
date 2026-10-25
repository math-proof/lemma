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
import Def.StatisticalMechanics.Code.Sharpness.CurrentRep.Part2
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000


namespace StatMech

namespace Sharpness

open StatMech.Ising


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem tsum_gEdge (β : ℝ) (J : Sym2 V → ℝ) (s : ConfigSpace V) (e : Sym2 V) :
    (∑' k, gEdge β J s e k) = Real.exp (β * J e * bond s e) := by
  unfold gEdge
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
  exact tsum_congr (fun k => by rw [smul_eq_mul, div_eq_inv_mul, ← mul_pow])


theorem summable_gEdge (β : ℝ) (J : Sym2 V → ℝ) (s : ConfigSpace V) (e : Sym2 V) :
    Summable (gEdge β J s e) := by
  unfold gEdge
  have h := NormedSpace.expSeries_summable' (𝕂 := ℝ) (β * J e * bond s e)
  convert h using 2 with k; rw [smul_eq_mul, div_eq_inv_mul, ← mul_pow]


theorem summable_norm_gEdge (β : ℝ) (J : Sym2 V → ℝ) (s : ConfigSpace V) (e : Sym2 V) :
    Summable (fun k => ‖gEdge β J s e k‖) := by
  unfold gEdge
  have h2 : Summable (fun k : ℕ => (|β * J e * bond s e|) ^ k / k.factorial) := by
    have := NormedSpace.expSeries_summable' (𝕂 := ℝ) (|β * J e * bond s e|)
    convert this using 2 with k; rw [smul_eq_mul, div_eq_inv_mul]
  refine h2.congr (fun k => ?_)
  rw [Real.norm_eq_abs, abs_div, ← mul_pow, abs_pow]
  congr 1
  exact (abs_of_nonneg (by positivity)).symm


theorem prod_gEdge (β : ℝ) (J : Sym2 V → ℝ) (s : ConfigSpace V) (m : ↥G.edgeFinset → ℕ) :
    (∏ e : ↥G.edgeFinset, gEdge β J s e.1 (m e))
      = weight G β J (ofEdgeFun G m) * ∏ e : ↥G.edgeFinset, (bond s e.1) ^ (m e) := by
  rw [weight_ofEdgeFun, ← Finset.prod_mul_distrib]
  unfold gEdge
  exact Finset.prod_congr rfl (fun e _ => by ring)


end Sharpness
end StatMech
