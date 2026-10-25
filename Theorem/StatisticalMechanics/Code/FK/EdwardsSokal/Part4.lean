/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.Potts.Part6
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FK.EdwardsSokal.Part4
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem esWeight_eq_prod_univ {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) :
    esWeight G p σ ω = ∏ e : Sym2 V, esCoeff G p σ e (ω e) := by
  have hstep : (∏ e ∈ G.edgeFinset, esCoeff G p σ e (ω e))
      = ∏ e : Sym2 V, esCoeff G p σ e (ω e) := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro e _ he
    unfold esCoeff
    rw [if_neg he]
  rw [← hstep]
  unfold esWeight esCoeff esEdgeFactor
  apply Finset.prod_congr rfl
  intro e he
  rw [if_pos he]


theorem esWeight_sum_omega {q : ℕ} (p : ℝ) (σ : V → Fin q) :
    (∑ ω : ConfigSpace (Sym2 V), esWeight G p σ ω)
      = ∏ e : Sym2 V, ∑ b : Bool, esCoeff G p σ e b := by
  have hrw : (∑ ω : ConfigSpace (Sym2 V), esWeight G p σ ω)
      = ∑ ω : ConfigSpace (Sym2 V), ∏ e : Sym2 V, esCoeff G p σ e (ω e) := by
    apply Finset.sum_congr rfl
    intro ω _
    exact esWeight_eq_prod_univ G p σ ω
  rw [hrw, ← Fintype.prod_sum]


theorem esCoeff_bool_sum {q : ℕ} (p : ℝ) (σ : V → Fin q) (e : Sym2 V) :
    (∑ b : Bool, esCoeff G p σ e b)
      = if e ∈ G.edgeFinset then (1 - p) + p * Potts.monoIndicator σ e else 2 := by
  unfold esCoeff
  rw [Fintype.sum_bool]
  by_cases he : e ∈ G.edgeFinset
  · simp only [if_pos he, if_true]
    norm_num
    ring
  · simp only [if_neg he]
    norm_num

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem edge_sum_eq_exp {q : ℕ} (β J : ℝ) (σ : V → Fin q) (e : Sym2 V) :
    (1 - (1 - Real.exp (-(β * J)))) + (1 - Real.exp (-(β * J))) * Potts.monoIndicator σ e
      = Real.exp (-(β * J)) * Real.exp (β * J * Potts.monoIndicator σ e) := by
  induction e with
  | _ x y =>
    rw [Potts.monoIndicator_mk]
    by_cases h : σ x = σ y
    · rw [if_pos h, mul_one, ← Real.exp_add]
      rw [show -(β * J) + β * J * 1 = 0 by ring, Real.exp_zero]
      ring
    · rw [if_neg h]
      simp only [mul_zero, Real.exp_zero, mul_one]
      ring


end FK
end StatMech
