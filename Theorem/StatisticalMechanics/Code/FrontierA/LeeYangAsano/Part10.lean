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
import Def.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part9
open scoped ComplexConjugate


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem leeYangChoiceTerm_eq_weight_monomial (beta : ℝ)
    (x : (V → Bool) × (↑G.edgeFinset → Bool × Bool))
    (z : LeeYangVar G → ℂ) :
    leeYangChoiceTerm G beta x z =
      leeYangChoiceWeight G beta x * leeYangMonomial (leeYangChoiceSupport G x) z := by
  unfold leeYangChoiceTerm leeYangChoiceWeight leeYangMonomial leeYangChoiceSupport
  rw [Finset.prod_filter]
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type]
  have hanchor :
      (∏ v : V, if leeYangChoiceSelected G x (Sum.inl v) = true
          then z (Sum.inl v) else 1) =
        ∏ v : V, leeYangAnchorChoiceFactor G z v (x.1 v) := by
    apply Finset.prod_congr rfl
    intro v hv
    cases hx : x.1 v <;> simp [leeYangChoiceSelected, leeYangAnchorChoiceFactor, hx,
      leeYangAnchor]
  rw [hanchor]
  have hhalf (e : ↑G.edgeFinset) :
      (∏ v : V, if leeYangChoiceSelected G x (Sum.inr (v, e)) = true
          then z (Sum.inr (v, e)) else 1) =
        (if (x.2 e).1 then z (leeYangHalf G (leeYangEndpoint0 G e) e) else 1) *
        (if (x.2 e).2 then z (leeYangHalf G (leeYangEndpoint1 G e) e) else 1) := by
    classical
    calc
      (∏ v : V, if leeYangChoiceSelected G x (Sum.inr (v, e)) = true
          then z (Sum.inr (v, e)) else 1) =
          ∏ v : V,
            (if (x.2 e).1 then
                (if leeYangEndpoint0 G e = v then z (Sum.inr (v, e)) else 1) else 1) *
            (if (x.2 e).2 then
                (if leeYangEndpoint1 G e = v then z (Sum.inr (v, e)) else 1) else 1) := by
        apply Finset.prod_congr rfl
        intro v hv
        by_cases hv0 : v = leeYangEndpoint0 G e
        · subst v
          simp [leeYangChoiceSelected, Ne.symm (leeYang_endpoints_ne G e)]
        · by_cases hv1 : v = leeYangEndpoint1 G e
          · subst v
            simp [leeYangChoiceSelected, leeYang_endpoints_ne G e,
              Ne.symm (leeYang_endpoints_ne G e)]
          · have hv0' : leeYangEndpoint0 G e ≠ v := Ne.symm hv0
            have hv1' : leeYangEndpoint1 G e ≠ v := Ne.symm hv1
            simp [leeYangChoiceSelected, hv0, hv1, hv0', hv1']
      _ = _ := by
        rw [Finset.prod_mul_distrib]
        by_cases h0 : (x.2 e).1 = true <;> by_cases h1 : (x.2 e).2 = true <;>
          simp [h0, h1, leeYangHalf]
  rw [Finset.prod_comm]
  simp_rw [hhalf]
  unfold leeYangEdgeChoiceFactor
  have hedgeprod :
      (∏ e : ↑G.edgeFinset,
        ((if (x.2 e).1 = (x.2 e).2 then 1 else (Real.exp (-2 * beta) : ℂ)) *
          (if (x.2 e).1 then z (leeYangHalf G (leeYangEndpoint0 G e) e) else 1)) *
          (if (x.2 e).2 then z (leeYangHalf G (leeYangEndpoint1 G e) e) else 1)) =
        (∏ e : ↑G.edgeFinset,
          if (x.2 e).1 = (x.2 e).2 then 1 else (Real.exp (-2 * beta) : ℂ)) *
        ∏ e : ↑G.edgeFinset,
          (if (x.2 e).1 then z (leeYangHalf G (leeYangEndpoint0 G e) e) else 1) *
          (if (x.2 e).2 then z (leeYangHalf G (leeYangEndpoint1 G e) e) else 1) := by
    calc
      _ = ∏ e : ↑G.edgeFinset,
          (if (x.2 e).1 = (x.2 e).2 then 1 else (Real.exp (-2 * beta) : ℂ)) *
          ((if (x.2 e).1 then z (leeYangHalf G (leeYangEndpoint0 G e) e) else 1) *
          (if (x.2 e).2 then z (leeYangHalf G (leeYangEndpoint1 G e) e) else 1)) := by
            apply Finset.prod_congr rfl
            intro e he
            ring
      _ = _ := Finset.prod_mul_distrib
  rw [hedgeprod]
  ring

theorem asanoContract_const_mul {I : Type*} [DecidableEq I]
    (c : ℂ) (p : (I → ℂ) → ℂ) (i j : I) :
    asanoContract (fun z ↦ c * p z) i j = fun z ↦ c * asanoContract p i j z := by
  funext z
  simp only [asanoContract]
  ring

theorem leeYangContractList_zero (L : List (V × ↑G.edgeFinset)) :
    leeYangContractList G L (fun _ ↦ 0) = fun _ ↦ 0 := by
  induction L with
  | nil => rfl
  | cons x L ih =>
      simp only [leeYangContractList, List.foldl_cons]
      rw [show asanoContract (fun _ : LeeYangVar G → ℂ ↦ 0)
          (leeYangAnchor G x.1) (leeYangHalf G x.1 x.2) = (fun _ ↦ 0) by
        funext z
        simp [asanoContract]]
      exact ih

theorem leeYangContractList_const_mul (L : List (V × ↑G.edgeFinset))
    (c : ℂ) (p : (LeeYangVar G → ℂ) → ℂ) :
    leeYangContractList G L (fun z ↦ c * p z) =
      fun z ↦ c * leeYangContractList G L p z := by
  induction L generalizing p with
  | nil => rfl
  | cons x L ih =>
      simp only [leeYangContractList, List.foldl_cons]
      rw [asanoContract_const_mul]
      exact ih _

end StatMech.FrontierA
