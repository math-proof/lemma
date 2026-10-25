/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalMultiaffine
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Def.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part7
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


theorem inhomogeneousIsingPartition_highTemperature
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (coupling : Sym2 V → Real) :
    StatMech.Sharpness.ZJ G.edgeFinset coupling (fun _ ↦ 0) =
      (2 : Real) ^ Fintype.card V *
        (∏ edge ∈ G.edgeFinset, Real.cosh (coupling edge)) *
        inhomogeneousEvenSubgraphSum G (fun edge ↦ Real.tanh (coupling edge)) := by
  classical
  open StatMech.Sharpness in
  unfold ZJ
  have hweight (s : ConfigSpace V) :
      wJ G.edgeFinset coupling (fun _ ↦ 0) s =
        (∏ edge ∈ G.edgeFinset, Real.cosh (coupling edge)) *
          ∏ edge ∈ G.edgeFinset,
            (1 + Real.tanh (coupling edge) * bond s edge) := by
    unfold wJ
    simp only [zero_mul, Finset.sum_const_zero, add_zero]
    rw [Real.exp_sum, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro edge _
    exact exp_mul_eq_cosh_mul (coupling edge) (bond s edge)
      (bond_eq_one_or_neg_one s edge)
  simp_rw [hweight]
  have hexpand (s : ConfigSpace V) :
      (∏ edge ∈ G.edgeFinset,
          (1 + Real.tanh (coupling edge) * bond s edge)) =
        ∑ F ∈ G.edgeFinset.powerset,
          ∏ edge ∈ F, Real.tanh (coupling edge) * bond s edge :=
    Finset.prod_one_add _
  simp_rw [hexpand]
  rw [← Finset.mul_sum, Finset.sum_comm]
  unfold inhomogeneousEvenSubgraphSum
  rw [show (2 : Real) ^ Fintype.card V *
        (∏ edge ∈ G.edgeFinset, Real.cosh (coupling edge)) *
          ∑ F ∈ evenSubgraphs G,
            ∏ edge ∈ F, Real.tanh (coupling edge) =
      (∏ edge ∈ G.edgeFinset, Real.cosh (coupling edge)) *
        ((2 : Real) ^ Fintype.card V *
          ∑ F ∈ evenSubgraphs G,
            ∏ edge ∈ F, Real.tanh (coupling edge)) by ring]
  congr 1
  unfold evenSubgraphs
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro F hF
  rw [Finset.mem_powerset] at hF
  have hpull (s : ConfigSpace V) :
      (∏ edge ∈ F, Real.tanh (coupling edge) * bond s edge) =
        (∏ edge ∈ F, Real.tanh (coupling edge)) *
          ∏ edge ∈ F, bond s edge := by
    rw [Finset.prod_mul_distrib]
  simp_rw [hpull]
  rw [← Finset.mul_sum]
  have hnondiag : ∀ edge ∈ F, ¬ edge.IsDiag := by
    intro edge hedge
    exact SimpleGraph.not_isDiag_of_mem_edgeSet G
      (by rw [← SimpleGraph.mem_edgeFinset]; exact hF hedge)
  rw [sum_prod_bond_subgraph F hnondiag]
  by_cases heven : IsEvenSubgraph F
  · rw [if_pos heven, if_pos heven]
    ring
  · rw [if_neg heven, if_neg heven]
    ring

theorem squareTorus_spinCharacter_arf_sum
    (h : Fin 2 × Fin 2) :
    (2 : Complex) =
      ons_spinCharacter 1 1 h + ons_spinCharacter 0 1 h +
        ons_spinCharacter 1 0 h - ons_spinCharacter 0 0 h := by
  rcases h with ⟨h₁, h₂⟩
  fin_cases h₁ <;> fin_cases h₂ <;>
    norm_num [ons_spinCharacter]


theorem two_mul_inhomogeneousEvenSubgraphSum_eq_spin
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Real) :
    (2 : Complex) * inhomogeneousEvenSubgraphSum (onsTorusGraph L) weight =
      ons_weightedSpinCharacterSum L (fun edge ↦ (weight edge : Complex)) 1 1 +
      ons_weightedSpinCharacterSum L (fun edge ↦ (weight edge : Complex)) 0 1 +
      ons_weightedSpinCharacterSum L (fun edge ↦ (weight edge : Complex)) 1 0 -
      ons_weightedSpinCharacterSum L (fun edge ↦ (weight edge : Complex)) 0 0 := by
  classical
  unfold inhomogeneousEvenSubgraphSum ons_weightedSpinCharacterSum
  push_cast
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro F hF
  rw [squareTorus_spinCharacter_arf_sum (ons_evenHomology L F)]
  ring

end StatMech.FrontierA
