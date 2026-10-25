/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempDual.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceClosure
import Def.StatisticalMechanics.Code.Onsager.SignedLoopLowTempKacWard.Part5
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

open StatMech.FrontierA

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E]

theorem kwg_indexedEvenPolynomial_eq_sum (ends : E -> Sym2 V)
    (x : E -> ℂ) :
    kwg_indexedEvenPolynomial ends x =
      ∑ F : KWGIndexedEvenSet ends, ∏ e ∈ F.1, x e := by
  unfold kwg_indexedEvenPolynomial
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    (Finset.univ.filter (kwg_IsEven ends))
    (fun F => by simp [KWGIndexedEvenSet])
    (fun F => ∏ e ∈ F, x e)


theorem kwg_subdiv_evenPolynomial_eq (ends : E -> Sym2 V) (x : E -> ℂ) :
    kwEvenPolynomial (kwg_subdivGraph ends) (kwg_subdivWeight (V := V) x) =
      kwg_indexedEvenPolynomial ends x := by
  rw [kwEvenPolynomial_eq_sum_actual,
    kwg_indexedEvenPolynomial_eq_sum]
  symm
  apply Fintype.sum_equiv (kwg_subdivEvenEquiv ends)
  intro F
  exact (kwg_subdivLift_weight_product ends x F.1).symm


theorem kwg_subdiv_kacWard_det
    (ends : E -> Sym2 V)
    (embedding : KWStraightLineEmbedding (kwg_subdivGraph ends))
    (x : E -> ℂ) :
    (1 - kwGraphTransition (kwg_subdivGraph ends)
      (kwg_subdivWeight (V := V) x) embedding.turnPhase).det =
        (kwg_indexedEvenPolynomial ends x) ^ 2 := by
  rw [kacWard_straightLine_arbitrary_adaptive,
    kwg_subdiv_evenPolynomial_eq]


theorem ofReal_kwg_lowTempDualSum_eq_indexedEvenPolynomial
    (P : PlanarZ2Subgraph) (beta : Real) :
    (kwg_lowTempDualSum P beta : ℂ) =
      kwg_indexedEvenPolynomial (kwg_dualEnds P)
        (fun _ => (Real.exp (-2 * beta) : ℂ)) := by
  unfold kwg_lowTempDualSum kwg_indexedEvenPolynomial
  push_cast
  apply Finset.sum_congr rfl
  intro F _
  by_cases hF : kwg_IsEven (kwg_dualEnds P) F <;> simp [hF]


theorem kwg_lowTempDualSum_sq_eq_kacWard_det
    (P : PlanarZ2Subgraph) (beta : Real)
    (embedding : KWStraightLineEmbedding
      (kwg_subdivGraph (kwg_dualEnds P))) :
    ((kwg_lowTempDualSum P beta : ℂ) ^ 2) =
      (1 - kwGraphTransition (kwg_subdivGraph (kwg_dualEnds P))
        (kwg_subdivWeight (V := kwg_Face P)
          (fun _ => (Real.exp (-2 * beta) : ℂ)))
        embedding.turnPhase).det := by
  rw [ofReal_kwg_lowTempDualSum_eq_indexedEvenPolynomial]
  exact (kwg_subdiv_kacWard_det (kwg_dualEnds P) embedding _).symm


end
end StatMech.Onsager
