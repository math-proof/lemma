/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc16core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Def.StatisticalMechanics.Code.Walls.gc16core.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.show false
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (S : SimpleGraph V) [DecidableRel S.Adj]


theorem gc16_inner_eq_splitWeightedSum (β : ℝ) (J : Sym2 V → ℝ)
    (p : ↥S.edgeFinset → ℕ) (A : Finset V) :
    (∑ K₁ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ p e},
        (if sources S (ofEdgeFun S K₁.1) = A then weight S β J (ofEdgeFun S K₁.1) else 0)
          * weight S β J (ofEdgeFun S (fun e => p e - K₁.1 e)))
      = splitWeightedSum S β J (ofEdgeFun S p) 1 A := by
  unfold splitWeightedSum
  rw [← Equiv.sum_comp (gc16_edgeNativeEquiv S p)]
  refine Finset.sum_congr rfl (fun K₁ _ => ?_)
  simp only [gc16_edgeNativeEquiv, Equiv.coe_fn_mk]
  
  have hsub : (ofEdgeFun S (fun e => p e - K₁.1 e))
      = (fun e => ofEdgeFun S p e - (ofEdgeFun S K₁.1) e) := by
    funext e
    simp only [ofEdgeFun]
    by_cases he : e ∈ S.edgeFinset <;> simp [he]
  rw [hsub]
  by_cases hA : sources S (ofEdgeFun S K₁.1) = A
  · rw [if_pos hA, if_pos hA, one_mul]
  · rw [if_neg hA, if_neg hA, zero_mul]


end StatMech.Walls
