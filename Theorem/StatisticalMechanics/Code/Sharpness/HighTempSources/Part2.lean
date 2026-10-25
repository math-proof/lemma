/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSources.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.KWSelfDuality.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePropsFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLieb.Part2
import Def.StatisticalMechanics.Code.Sharpness.HighTempSources.Part2
open Finset
open scoped BigOperators


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem boltzmannJ_high_temp_factor (beta : ℝ) (J : Sym2 V → ℝ)
    (s : ConfigSpace V) :
    boltzmannJ G beta J s =
      (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
        ∏ e ∈ G.edgeFinset,
          (1 + Real.tanh (beta * J e) * bond s e) := by
  unfold boltzmannJ
  rw [Finset.mul_sum, Real.exp_sum]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  rw [show beta * (J e * bond s e) = (beta * J e) * bond s e by ring]
  exact exp_mul_eq_cosh_mul (beta * J e) (bond s e)
    (bond_eq_one_or_neg_one s e)


theorem spinProd_boltzmannJ_high_temp_expansion (beta : ℝ)
    (J : Sym2 V → ℝ) (A : Finset V) :
    (∑ s : ConfigSpace V, spinProd A s * boltzmannJ G beta J s) =
      (2 : ℝ) ^ Fintype.card V *
        (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
        ∑ F ∈ G.edgeFinset.powerset.filter (fun F => HasOddBoundary F A),
          highTempSubgraphWeight beta J F := by
  simp_rw [boltzmannJ_high_temp_factor G beta J]
  have hexpand : ∀ s : ConfigSpace V,
      (∏ e ∈ G.edgeFinset,
          (1 + Real.tanh (beta * J e) * bond s e)) =
        ∑ F ∈ G.edgeFinset.powerset,
          ∏ e ∈ F, (Real.tanh (beta * J e) * bond s e) := by
    intro s
    exact Finset.prod_one_add _
  simp_rw [hexpand]
  have hswap :
      (∑ s : ConfigSpace V,
        spinProd A s *
          ((∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
            ∑ F ∈ G.edgeFinset.powerset,
              ∏ e ∈ F, (Real.tanh (beta * J e) * bond s e))) =
        (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
          ∑ F ∈ G.edgeFinset.powerset,
            ∑ s : ConfigSpace V, spinProd A s *
              ∏ e ∈ F, (Real.tanh (beta * J e) * bond s e) := by
    calc
      _ = (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
          ∑ s : ConfigSpace V, spinProd A s *
            (∑ F ∈ G.edgeFinset.powerset,
              ∏ e ∈ F, (Real.tanh (beta * J e) * bond s e)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s _
            ring
      _ = (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
          ∑ s : ConfigSpace V, ∑ F ∈ G.edgeFinset.powerset,
            spinProd A s *
              ∏ e ∈ F, (Real.tanh (beta * J e) * bond s e) := by
            congr 1
            apply Finset.sum_congr rfl
            intro s _
            rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_comm]
  rw [hswap, Finset.sum_filter]
  rw [show
      (2 : ℝ) ^ Fintype.card V *
          (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
          (∑ F ∈ G.edgeFinset.powerset,
            if HasOddBoundary F A then highTempSubgraphWeight beta J F else 0) =
        (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) *
          ((2 : ℝ) ^ Fintype.card V *
            ∑ F ∈ G.edgeFinset.powerset,
              if HasOddBoundary F A then highTempSubgraphWeight beta J F else 0) by
        ring]
  apply congrArg ((∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) * ·)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [Finset.mem_powerset] at hF
  have hpull : ∀ s : ConfigSpace V,
      spinProd A s *
          ∏ e ∈ F, (Real.tanh (beta * J e) * bond s e) =
        highTempSubgraphWeight beta J F *
          (spinProd A s * ∏ e ∈ F, bond s e) := by
    intro s
    unfold highTempSubgraphWeight
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [hpull, ← Finset.mul_sum]
  have hnd : ∀ e ∈ F, ¬ e.IsDiag := by
    intro e he
    exact SimpleGraph.not_isDiag_of_mem_edgeSet G
      (by rw [← SimpleGraph.mem_edgeFinset]; exact hF he)
  rw [sum_spinProd_prod_bond_subgraph A F hnd]
  by_cases hbd : HasOddBoundary F A
  · rw [if_pos hbd, if_pos hbd]
    ring
  · rw [if_neg hbd, if_neg hbd]
    ring


theorem expectationJ_high_temp_ratio (beta : ℝ) (J : Sym2 V → ℝ)
    (A : Finset V) :
    expectationJ G beta J A =
      (∑ F ∈ G.edgeFinset.powerset.filter (fun F => HasOddBoundary F A),
          highTempSubgraphWeight beta J F) /
        (∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
          highTempSubgraphWeight beta J F) := by
  unfold expectationJ partitionJ
  rw [spinProd_boltzmannJ_high_temp_expansion G beta J A]
  rw [show (∑ s : ConfigSpace V, boltzmannJ G beta J s) =
      ∑ s : ConfigSpace V, spinProd (∅ : Finset V) s *
        boltzmannJ G beta J s by
      apply Finset.sum_congr rfl
      intro s _
      simp]
  rw [spinProd_boltzmannJ_high_temp_expansion G beta J ∅]
  simp_rw [hasOddBoundary_empty]
  have htwo : (2 : ℝ) ^ Fintype.card V ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcosh : (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro e _
    exact ne_of_gt (Real.cosh_pos (beta * J e))
  field_simp


end Sharpness
end StatMech
