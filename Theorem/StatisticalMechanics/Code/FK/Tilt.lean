/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Tilt.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FK.Tilt
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [DecidableEq V] in

theorem openCount_add_closedCount (ω : ConfigSpace (Sym2 V)) :
    openCount G ω + closedCount G ω = G.edgeFinset.card := by
  unfold openCount closedCount
  have hfilt : G.edgeFinset.filter (fun e => ω e = false)
      = G.edgeFinset.filter (fun e => ¬ ω e = true) := by
    apply Finset.filter_congr; intro e _; simp [Bool.not_eq_true]
  rw [hfilt, Finset.card_filter_add_card_filter_not]

omit [DecidableEq V] in


theorem edgeProduct_eq_pow (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    edgeProduct G p ω = p ^ openCount G ω * (1 - p) ^ closedCount G ω := by
  unfold edgeProduct openCount closedCount
  rw [← Finset.prod_filter_mul_prod_filter_not G.edgeFinset (fun e => ω e = true)]
  congr 1
  · rw [Finset.prod_congr rfl (fun e he => if_pos (Finset.mem_filter.1 he).2),
      Finset.prod_const]
  · have hfilt : G.edgeFinset.filter (fun e => ¬ ω e = true)
        = G.edgeFinset.filter (fun e => ω e = false) := by
      apply Finset.filter_congr; intro e _; simp [Bool.not_eq_true]
    rw [Finset.prod_congr rfl (fun e he => if_neg (Finset.mem_filter.1 he).2),
      Finset.prod_const, hfilt]


end FK
end StatMech
