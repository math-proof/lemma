/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempDual.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceClosure
import Def.StatisticalMechanics.Code.Onsager.SignedLoopLowTempKacWard.Part6
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

open StatMech.FrontierA

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E]

theorem kwg_sum_countEq_eq_countP {A : Type*} [DecidableEq A]
    (F : Finset A) (l : List A) :
    (∑ e ∈ F, l.countP (fun a => decide (a = e))) =
      l.countP (fun a => decide (a ∈ F)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.countP_cons]
      simp_rw [List.countP_cons]
      rw [Finset.sum_add_distrib, ih]
      by_cases ha : a ∈ F <;> simp [ha]


theorem ofReal_kwg_pathDefectSign_eq_prod_pathEdgeSign
    (P : PlanarZ2Subgraph) {u v : P.V} (path : P.G.Walk u v)
    (F : Finset (kwg_Edge P)) :
    (kwg_pathDefectSign P path F : ℂ) =
      ∏ e ∈ F, kwg_pathEdgeSign P path e := by
  unfold kwg_pathDefectSign kwg_pathDefectCount kwg_pathEdgeSign
  calc
    ((if Even ((kwg_pathEdgeIndices P path).countP
        fun edge => decide (edge ∈ F)) then (1 : Real) else -1 : Real) : ℂ) =
        (if Even ((kwg_pathEdgeIndices P path).countP
          fun edge => decide (edge ∈ F)) then (1 : ℂ) else -1) := by
      split_ifs <;> norm_num
    _ = (-1 : ℂ) ^ ((kwg_pathEdgeIndices P path).countP
          fun edge => decide (edge ∈ F)) := neg_one_pow_eq_ite.symm
    _ = (-1 : ℂ) ^
        (∑ e ∈ F, (kwg_pathEdgeIndices P path).countP
          (fun a => decide (a = e))) := by
      congr 1
      exact (kwg_sum_countEq_eq_countP F
        (kwg_pathEdgeIndices P path)).symm
    _ = ∏ e ∈ F,
        (-1 : ℂ) ^ (kwg_pathEdgeIndices P path).countP
          (fun a => decide (a = e)) := by
      rw [Finset.prod_pow_eq_pow_sum]


theorem ofReal_kwg_lowTempPathDualSum_eq_indexedEvenPolynomial
    (P : PlanarZ2Subgraph) (beta : Real)
    {u v : P.V} (path : P.G.Walk u v) :
    (kwg_lowTempPathDualSum P beta path : ℂ) =
      kwg_indexedEvenPolynomial (kwg_dualEnds P)
        (fun e => kwg_pathEdgeSign P path e *
          (Real.exp (-2 * beta) : ℂ)) := by
  unfold kwg_lowTempPathDualSum kwg_indexedEvenPolynomial
  push_cast
  apply Finset.sum_congr rfl
  intro F _
  by_cases hF : kwg_IsEven (kwg_dualEnds P) F
  · simp only [hF, if_true]
    rw [Finset.prod_mul_distrib,
      ← ofReal_kwg_pathDefectSign_eq_prod_pathEdgeSign]
    simp
  · simp [hF]


theorem kwg_lowTempPathDualSum_sq_eq_kacWard_det
    (P : PlanarZ2Subgraph) (beta : Real)
    {u v : P.V} (path : P.G.Walk u v)
    (embedding : KWStraightLineEmbedding
      (kwg_subdivGraph (kwg_dualEnds P))) :
    ((kwg_lowTempPathDualSum P beta path : ℂ) ^ 2) =
      (1 - kwGraphTransition (kwg_subdivGraph (kwg_dualEnds P))
        (kwg_subdivWeight (V := kwg_Face P)
          (fun e => kwg_pathEdgeSign P path e *
            (Real.exp (-2 * beta) : ℂ)))
        embedding.turnPhase).det := by
  rw [ofReal_kwg_lowTempPathDualSum_eq_indexedEvenPolynomial]
  exact (kwg_subdiv_kacWard_det (kwg_dualEnds P) embedding _).symm

end
end StatMech.Onsager
