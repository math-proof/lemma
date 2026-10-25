/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.LeeYangPolynomial
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
import Theorem.StatisticalMechanics.Code.FrontierC.LeeYangSymmetry.Part2
import Def.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part12
open scoped ComplexConjugate


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem leeYangEraseHalves_choiceSupport
    (sigma : V → Bool) (tau : ↑G.edgeFinset → Bool × Bool) :
    leeYangEraseHalves G (leeYangIncidenceFinset G).toList
        (leeYangChoiceSupport G (sigma, tau)) =
      leeYangAnchorSupport G sigma := by
  ext k
  rw [mem_leeYangEraseHalves]
  rcases k with v | ⟨v, e⟩
  · simp [leeYangAnchorSupport, leeYangChoiceSupport, leeYangChoiceSelected,
      leeYangHalf]
  · simp only [leeYangAnchorSupport, Finset.mem_filter, Finset.mem_univ,
      true_and, iff_false]
    intro h
    rcases h with ⟨hsupport, herased⟩
    have hselected : leeYangChoiceSelected G (sigma, tau) (Sum.inr (v, e)) = true := by
      simpa [leeYangChoiceSupport] using hsupport
    have hv : v = leeYangEndpoint0 G e ∨ v = leeYangEndpoint1 G e := by
      unfold leeYangChoiceSelected at hselected
      by_cases h0 : v = leeYangEndpoint0 G e
      · exact Or.inl h0
      · by_cases h1 : v = leeYangEndpoint1 G e
        · exact Or.inr h1
        · simp [h0, h1] at hselected
    apply herased (v, e)
    · rw [Finset.mem_toList, leeYang_incidence_pair_mem]
      rcases hv with rfl | rfl
      · exact Sym2.out_fst_mem e.1
      · exact Sym2.out_snd_mem e.1
    · rfl

theorem leeYangContractedProduct_eq_sum_choices (beta : ℝ)
    (z : LeeYangVar G → ℂ) :
    leeYangContractedProduct G beta z =
      ∑ x : (V → Bool) × (↑G.edgeFinset → Bool × Bool),
        if x.2 = leeYangTauOf G x.1 then
          leeYangChoiceWeight G beta x *
            leeYangMonomial (leeYangAnchorSupport G x.1) z
        else 0 := by
  unfold leeYangContractedProduct
  rw [leeYangHalfEdgeProduct_eq_sum_choices G beta]
  rw [leeYangContractList_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hterm : leeYangChoiceTerm G beta x = fun w ↦
      leeYangChoiceWeight G beta x *
        leeYangMonomial (leeYangChoiceSupport G x) w := by
    funext w
    exact leeYangChoiceTerm_eq_weight_monomial G beta x w
  rw [hterm]
  rw [leeYangContractList_const_mul]
  change leeYangChoiceWeight G beta x *
      leeYangContractList G (leeYangIncidenceFinset G).toList
        (leeYangMonomial (leeYangChoiceSupport G x)) z = _
  rw [leeYangContractList_monomial G _ (Finset.nodup_toList _) _]
  rw [leeYangChoiceSupport_consistent_iff,
    leeYangEraseHalves_choiceSupport]
  by_cases h : x.2 = leeYangTauOf G x.1 <;> simp [h]

theorem leeYangContractedProduct_eq_sum_sigma (beta : ℝ)
    (z : LeeYangVar G → ℂ) :
    leeYangContractedProduct G beta z =
      ∑ sigma : V → Bool,
        leeYangChoiceWeight G beta (sigma, leeYangTauOf G sigma) *
          leeYangMonomial (leeYangAnchorSupport G sigma) z := by
  rw [leeYangContractedProduct_eq_sum_choices]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro sigma hsigma
  rw [Fintype.sum_eq_single (leeYangTauOf G sigma)]
  · simp
  · simp_all

end StatMech.FrontierA
