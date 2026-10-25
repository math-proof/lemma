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
import Instance.StatisticalMechanics.Code.Sharpness.HighTempSources
open Finset
open scoped BigOperators


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


omit [Fintype V] in
@[simp]
theorem hasOddBoundary_empty (F : Finset (Sym2 V)) :
    HasOddBoundary F ∅ ↔ IsEvenSubgraph F := by
  simp only [HasOddBoundary, IsEvenSubgraph, Finset.notMem_empty, iff_false,
    Nat.not_odd_iff_even]


theorem sum_spinProd_prod_bond_subgraph (A : Finset V) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    (∑ s : ConfigSpace V, spinProd A s * ∏ e ∈ F, bond s e)
      = if HasOddBoundary F A then (2 : ℝ) ^ Fintype.card V else 0 := by
  have hint : ∀ s : ConfigSpace V,
      spinProd A s * ∏ e ∈ F, bond s e =
        ∏ v : V, (spin s v) ^ (incCount F v + if v ∈ A then 1 else 0) := by
    intro s
    rw [spinProd_eq_prod_pow, prod_bond_eq_prod_pow_incCount s F hF,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun v _ => by rw [pow_add]; ring)
  simp_rw [hint]
  rw [sum_prod_spin_pow]
  simp_rw [sum_spinB_pow]
  by_cases hbd : HasOddBoundary F A
  · rw [if_pos hbd]
    have heven : ∀ v : V, Even (incCount F v + if v ∈ A then 1 else 0) := by
      intro v
      by_cases hv : v ∈ A
      · rw [if_pos hv, Nat.even_add_one, Nat.not_even_iff_odd]
        exact (hbd v).2 hv
      · rw [if_neg hv, add_zero]
        exact Nat.not_odd_iff_even.mp (fun hodd => hv ((hbd v).1 hodd))
    simp_rw [if_pos (heven _)]
    rw [Finset.prod_const, Finset.card_univ]
  · rw [if_neg hbd]
    have hex : ∃ v : V, ¬ (Odd (incCount F v) ↔ v ∈ A) := by
      simpa only [HasOddBoundary, not_forall] using hbd
    obtain ⟨v, hv⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    rw [if_neg]
    by_cases hvmem : v ∈ A
    · rw [if_pos hvmem, Nat.even_add_one, Nat.not_even_iff_odd]
      simpa [hvmem] using hv
    · rw [if_neg hvmem, add_zero, Nat.not_even_iff_odd]
      simpa [hvmem] using hv


theorem spinProd_weight_high_temp_expansion (beta : ℝ) (A : Finset V) :
    (∑ s : ConfigSpace V, spinProd A s * isingWeight G beta 0 s)
      = (2 : ℝ) ^ Fintype.card V * (Real.cosh beta) ^ G.edgeFinset.card
        * ∑ F ∈ G.edgeFinset.powerset.filter (fun F => HasOddBoundary F A),
            (Real.tanh beta) ^ F.card := by
  have hweight : ∀ s : ConfigSpace V,
      isingWeight G beta 0 s =
        (Real.cosh beta) ^ G.edgeFinset.card
          * ∏ e ∈ G.edgeFinset, (1 + Real.tanh beta * bond s e) := by
    intro s
    rw [isingWeight_field_free_eq_prod, prod_exp_bond_eq]
  simp_rw [hweight]
  have hexpand : ∀ s : ConfigSpace V,
      (∏ e ∈ G.edgeFinset, (1 + Real.tanh beta * bond s e)) =
        ∑ F ∈ G.edgeFinset.powerset,
          ∏ e ∈ F, (Real.tanh beta * bond s e) := by
    intro s
    exact Finset.prod_one_add _
  simp_rw [hexpand]
  have hswap : (∑ s : ConfigSpace V,
        spinProd A s * ((Real.cosh beta) ^ G.edgeFinset.card *
          ∑ F ∈ G.edgeFinset.powerset,
            ∏ e ∈ F, (Real.tanh beta * bond s e))) =
      (Real.cosh beta) ^ G.edgeFinset.card *
        ∑ F ∈ G.edgeFinset.powerset,
          ∑ s : ConfigSpace V, spinProd A s *
            ∏ e ∈ F, (Real.tanh beta * bond s e) := by
    calc
      _ = (Real.cosh beta) ^ G.edgeFinset.card *
          ∑ s : ConfigSpace V, spinProd A s *
            (∑ F ∈ G.edgeFinset.powerset,
              ∏ e ∈ F, (Real.tanh beta * bond s e)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s _
            ring
      _ = (Real.cosh beta) ^ G.edgeFinset.card *
          ∑ s : ConfigSpace V, ∑ F ∈ G.edgeFinset.powerset,
            spinProd A s * ∏ e ∈ F, (Real.tanh beta * bond s e) := by
            congr 1
            apply Finset.sum_congr rfl
            intro s _
            rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_comm]
  rw [hswap]
  rw [Finset.sum_filter]
  rw [show (2 : ℝ) ^ Fintype.card V * (Real.cosh beta) ^ G.edgeFinset.card *
      (∑ F ∈ G.edgeFinset.powerset,
        if HasOddBoundary F A then (Real.tanh beta) ^ F.card else 0) =
      (Real.cosh beta) ^ G.edgeFinset.card *
        ((2 : ℝ) ^ Fintype.card V *
          ∑ F ∈ G.edgeFinset.powerset,
            if HasOddBoundary F A then (Real.tanh beta) ^ F.card else 0) by ring]
  apply congrArg ((Real.cosh beta) ^ G.edgeFinset.card * ·)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [Finset.mem_powerset] at hF
  have hpull : ∀ s : ConfigSpace V,
      spinProd A s * ∏ e ∈ F, (Real.tanh beta * bond s e) =
        (Real.tanh beta) ^ F.card *
          (spinProd A s * ∏ e ∈ F, bond s e) := by
    intro s
    rw [Finset.prod_mul_distrib, Finset.prod_const]
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


theorem expectation_spinProd_high_temp_ratio (beta : ℝ) (A : Finset V) :
    isingExpectation G beta 0 (spinProd A) =
      (∑ F ∈ G.edgeFinset.powerset.filter (fun F => HasOddBoundary F A),
          (Real.tanh beta) ^ F.card) /
        (∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
          (Real.tanh beta) ^ F.card) := by
  unfold isingExpectation isingProb
  rw [show (∑ s : ConfigSpace V, isingWeight G beta 0 s / isingZ G beta 0 * spinProd A s) =
      (∑ s : ConfigSpace V, spinProd A s * isingWeight G beta 0 s) / isingZ G beta 0 by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    ring]
  rw [spinProd_weight_high_temp_expansion G beta A, isingZ_high_temp_expansion G beta]
  have htwo : (2 : ℝ) ^ Fintype.card V ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcosh : (Real.cosh beta) ^ G.edgeFinset.card ≠ 0 :=
    pow_ne_zero _ (ne_of_gt (Real.cosh_pos beta))
  field_simp


end Sharpness
end StatMech
