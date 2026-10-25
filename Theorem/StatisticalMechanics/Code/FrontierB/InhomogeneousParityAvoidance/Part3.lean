/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousParityAvoidance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentConditionalPMF.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
import Def.StatisticalMechanics.Code.FrontierB.InhomogeneousParityAvoidance.Part3
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem exp_neg_weightedEdgeSpinSum_eq_spinProd_sum
    (beta : ℝ) (J : Sym2 V → ℝ)
    (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬e.IsDiag)
    (s : ConfigSpace V) :
    Real.exp (-weightedEdgeSpinSum beta J F s) =
      ∑ T ∈ F.powerset,
        weightedEdgeExpansionCoeff beta J F T *
          spinProd (edgeBoundary (F \ T)) s := by
  unfold weightedEdgeSpinSum
  rw [show -(∑ e ∈ F, beta * J e * bond s e) =
      ∑ e ∈ F, -(beta * J e) * bond s e by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e he
    ring]
  rw [Real.exp_sum]
  simp_rw [exp_mul_pm (-(beta * J _)) (bond s _) (bond_eq_pm s _)]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro T hT
  unfold weightedEdgeExpansionCoeff
  rw [Finset.prod_mul_distrib,
    prod_bond_eq_spinProd_edgeBoundary (F \ T)]
  · ring
  · intro e he
    exact hF e (Finset.mem_sdiff.mp he).1


theorem expJ_exp_neg_weightedEdgeSpinSum
    (E : Finset (Sym2 V)) (K hfJ : Sym2 V → ℝ)
    (hf : V → ℝ) (beta : ℝ)
    (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬e.IsDiag) :
    expJ E K hf
        (fun s => Real.exp (-weightedEdgeSpinSum beta hfJ F s)) =
      ∑ T ∈ F.powerset,
        weightedEdgeExpansionCoeff beta hfJ F T *
          expJ E K hf (spinProd (edgeBoundary (F \ T))) := by
  unfold expJ
  have hnum :
      (∑ s : ConfigSpace V,
          Real.exp (-weightedEdgeSpinSum beta hfJ F s) * wJ E K hf s) =
        ∑ T ∈ F.powerset,
          weightedEdgeExpansionCoeff beta hfJ F T *
            ∑ s : ConfigSpace V,
              spinProd (edgeBoundary (F \ T)) s * wJ E K hf s := by
    simp_rw [exp_neg_weightedEdgeSpinSum_eq_spinProd_sum beta hfJ F hF]
    calc
      (∑ s : ConfigSpace V,
          (∑ T ∈ F.powerset,
            weightedEdgeExpansionCoeff beta hfJ F T *
              spinProd (edgeBoundary (F \ T)) s) * wJ E K hf s) =
        ∑ s : ConfigSpace V, ∑ T ∈ F.powerset,
          weightedEdgeExpansionCoeff beta hfJ F T *
            (spinProd (edgeBoundary (F \ T)) s * wJ E K hf s) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro T hT
          ring
      _ = ∑ T ∈ F.powerset, ∑ s : ConfigSpace V,
          weightedEdgeExpansionCoeff beta hfJ F T *
            (spinProd (edgeBoundary (F \ T)) s * wJ E K hf s) := by
          rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [← Finset.mul_sum]
  rw [hnum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro T hT
  ring

end StatMech.FrontierB
