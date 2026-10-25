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
import Def.StatisticalMechanics.Code.FK.EdwardsSokal.Part5
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [DecidableEq V] in
theorem esFirstConst_pos (β J : ℝ) : 0 < esFirstConst G β J := by
  unfold esFirstConst
  exact mul_pos (pow_pos (by norm_num) _) (pow_pos (Real.exp_pos _) _)


theorem esWeight_sum_eq_pottsWeight {q : ℕ} (β J : ℝ) (σ : V → Fin q) :
    (∑ ω : ConfigSpace (Sym2 V), esWeight G (1 - Real.exp (-(β * J))) σ ω)
      = esFirstConst G β J * Potts.pottsWeight G β J σ := by
  set p := 1 - Real.exp (-(β * J)) with hp
  rw [esWeight_sum_omega]
  have hcoeff : ∀ e : Sym2 V, (∑ b : Bool, esCoeff G p σ e b)
      = if e ∈ G.edgeFinset then
          Real.exp (-(β * J)) * Real.exp (β * J * Potts.monoIndicator σ e) else 2 := by
    intro e
    rw [esCoeff_bool_sum]
    by_cases he : e ∈ G.edgeFinset
    · rw [if_pos he, if_pos he, hp]
      exact edge_sum_eq_exp β J σ e
    · rw [if_neg he, if_neg he]
  rw [Finset.prod_congr rfl (fun e _ => hcoeff e)]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ G.edgeFinset)]
  have hedge : (∏ e ∈ Finset.univ.filter (· ∈ G.edgeFinset),
        if e ∈ G.edgeFinset then
          Real.exp (-(β * J)) * Real.exp (β * J * Potts.monoIndicator σ e) else 2)
      = Real.exp (-(β * J)) ^ G.edgeFinset.card * Potts.pottsWeight G β J σ := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [Finset.prod_congr rfl (fun e he => if_pos he)]
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    unfold Potts.pottsWeight Potts.agreement
    rw [← Real.exp_sum, Finset.mul_sum]
  have hnon : (∏ e ∈ Finset.univ.filter (fun e => ¬ e ∈ G.edgeFinset),
        if e ∈ G.edgeFinset then
          Real.exp (-(β * J)) * Real.exp (β * J * Potts.monoIndicator σ e) else 2)
      = 2 ^ (Fintype.card (Sym2 V) - G.edgeFinset.card) := by
    rw [Finset.prod_congr rfl (fun e he => if_neg (Finset.mem_filter.1 he).2)]
    rw [Finset.prod_const]
    congr 1
    rw [Finset.filter_not, Finset.card_sdiff]
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_univ, Finset.inter_univ]
  rw [hedge, hnon]
  unfold esFirstConst
  ring


end FK
end StatMech
