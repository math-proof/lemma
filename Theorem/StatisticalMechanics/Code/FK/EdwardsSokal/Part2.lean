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
import Instance.StatisticalMechanics.Code.FK.EdwardsSokal
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem constOnOpen_reachable {q : ℕ} (ω : ConfigSpace (Sym2 V)) (σ : V → Fin q)
    (h : ConstOnOpen G ω σ) {x y : V} (r : (openSub G ω).Reachable x y) : σ x = σ y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at r
  induction r with
  | refl => rfl
  | tail _ hab ih => rw [ih]; exact h _ _ hab

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem esEdgeFactor_eq {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) (e : Sym2 V) :
    esEdgeFactor p σ ω e =
      (if ω e then p else 1 - p) * (if ω e then Potts.monoIndicator σ e else 1) := by
  unfold esEdgeFactor
  split
  · ring
  · ring

omit [DecidableEq V] in


theorem esWeight_factor {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) :
    esWeight G p σ ω = edgeProduct G p ω *
      ∏ e ∈ G.edgeFinset, (if ω e then Potts.monoIndicator σ e else 1) := by
  unfold esWeight edgeProduct
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun e _ => esEdgeFactor_eq p σ ω e

omit [DecidableEq V] in


theorem monoProd_eq_indicator {q : ℕ} (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) :
    (∏ e ∈ G.edgeFinset, (if ω e then Potts.monoIndicator σ e else 1)) =
      if ConstOnOpen G ω σ then 1 else 0 := by
  by_cases h : ConstOnOpen G ω σ
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro e he
    induction e with
    | _ x y =>
      by_cases hω : ω s(x, y) = true
      · rw [if_pos hω, Potts.monoIndicator_mk]
        have hadj : (openSub G ω).Adj x y :=
          ⟨(SimpleGraph.mem_edgeFinset.1 he), hω⟩
        rw [if_pos (h x y hadj)]
      · simp only [Bool.not_eq_true] at hω
        rw [if_neg (by rw [hω]; simp)]
  · rw [if_neg h]
    rw [Finset.prod_eq_zero_iff]
    simp only [ConstOnOpen, not_forall] at h
    obtain ⟨x, y, hadj, hne⟩ := h
    refine ⟨s(x, y), ?_, ?_⟩
    · exact SimpleGraph.mem_edgeFinset.2 hadj.1
    · rw [if_pos hadj.2, Potts.monoIndicator_mk, if_neg hne]


end FK
end StatMech
