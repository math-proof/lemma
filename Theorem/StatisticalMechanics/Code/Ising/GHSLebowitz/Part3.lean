/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GHSDuplicateVariable.Part4
import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Def.StatisticalMechanics.Code.Ising.GHSLebowitz.Part2
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem mem_ghsLAgreeFinset (q : ConfigSpace V) (v : V) :
    v ∈ ghsLAgreeFinset q ↔ q v = true := by
  simp [ghsLAgreeFinset]

theorem ghsLAgreeFinset_monotone : Monotone (ghsLAgreeFinset : ConfigSpace V → Finset V) := by
  intro q r hqr v hv
  rw [mem_ghsLAgreeFinset] at hv ⊢
  have := hqr v
  cases hr : r v
  · exact False.elim ((not_lt_of_ge this) (by simpa [hv, hr] using Bool.false_lt_true))
  · rfl

@[simp] theorem ghsLAgreeFinset_sup (q r : ConfigSpace V) :
    ghsLAgreeFinset (q ⊔ r) = ghsLAgreeFinset q ∪ ghsLAgreeFinset r := by
  ext v
  cases hq : q v <;> cases hr : r v <;> simp [ghsLAgreeFinset, hq, hr]

@[simp] theorem ghsLAgreeFinset_inf (q r : ConfigSpace V) :
    ghsLAgreeFinset (q ⊓ r) = ghsLAgreeFinset q ∩ ghsLAgreeFinset r := by
  ext v
  cases hq : q v <;> cases hr : r v <;> simp [ghsLAgreeFinset, hq, hr]


theorem ghsL_bond_add_mate (q a : ConfigSpace V) (e : Sym2 V) :
    bond a e + bond (ghsLMate q a) e =
      if Sharpness.edgeInside (ghsLAgreeFinset q) e then 2 * bond a e
      else if Sharpness.edgeInside (ghsLAgreeFinset q)ᶜ e then 2 * bond a e
      else 0 := by
  induction e with
  | h x y =>
      simp only [bond_mk]
      unfold ghsLMate spin Sharpness.edgeInside
      by_cases hx : q x <;> by_cases hy : q y <;>
        cases hax : a x <;> cases hay : a y <;>
        norm_num [mem_ghsLAgreeFinset, hx, hy, hax, hay]


theorem ghsL_spin_add_mate (q a : ConfigSpace V) (v : V) :
    spin a v + spin (ghsLMate q a) v =
      if q v then 2 * spin a v else 0 := by
  unfold ghsLMate spin
  by_cases hq : q v <;> cases ha : a v <;> norm_num [hq, ha]


theorem ghsL_bondSum_split (q a : ConfigSpace V) :
    (∑ e ∈ G.edgeFinset, bond a e) +
        ∑ e ∈ G.edgeFinset, bond (ghsLMate q a) e =
      2 * (∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q), bond a e)
        + 2 * (∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ, bond a e) := by
  rw [← Finset.sum_add_distrib]
  simp_rw [ghsL_bond_add_mate]
  unfold ghsvp_vertexEdges
  rw [Finset.mul_sum, Finset.mul_sum]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hA : Sharpness.edgeInside (ghsLAgreeFinset q) e
  · have hAc : ¬ Sharpness.edgeInside (ghsLAgreeFinset q)ᶜ e := by
      induction e with
      | h x y => simp_all [Sharpness.edgeInside]
    simp [hA, hAc]
  · by_cases hAc : Sharpness.edgeInside (ghsLAgreeFinset q)ᶜ e
    · simp [hA, hAc]
    · simp [hA, hAc]


theorem ghsL_spinSum_split (q a : ConfigSpace V) :
    (∑ v : V, spin a v) + ∑ v : V, spin (ghsLMate q a) v =
      2 * ∑ v ∈ ghsLAgreeFinset q, spin a v := by
  rw [← Finset.sum_add_distrib]
  simp_rw [ghsL_spin_add_mate]
  rw [Finset.mul_sum]
  simp [ghsLAgreeFinset, Finset.sum_filter]


end Ising
end StatMech
