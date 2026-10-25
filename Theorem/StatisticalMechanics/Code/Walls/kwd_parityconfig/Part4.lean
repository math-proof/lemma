/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Walls.kwd_parityconfig.Part4
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Walls

section ParityProp

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (δ : Finset (Sym2 V))


variable {G δ}

omit [Fintype V] [DecidableRel G.Adj] in


theorem parityProp_adj_xor (hev : EvenOnAllCycles G δ) (hG : G.Preconnected) (v₀ : V)
    {x y : V} (h : G.Adj x y) :
    (parityProp G δ hG v₀ x).xor (parityProp G δ hG v₀ y) = decide (s(x, y) ∈ δ) := by
  let px : G.Walk v₀ x := (hG v₀ x).some
  let walkVy : G.Walk v₀ y := px.append (SimpleGraph.Walk.cons h (.nil : G.Walk y y))
  have hpar : parityProp G δ hG v₀ y = walkPar G δ walkVy :=
    walkPar_eq_of_evenOnAllCycles hev (hG v₀ y).some walkVy
  have hwalkVy : walkPar G δ walkVy
      = (parityProp G δ hG v₀ x).xor (decide (s(x, y) ∈ δ)) := by
    rw [walkPar_append, walkPar_singleton]; rfl
  rw [hpar, hwalkVy]
  cases parityProp G δ hG v₀ x <;> cases hb : decide (s(x, y) ∈ δ) <;> simp


theorem disagree_parityProp (hev : EvenOnAllCycles G δ) (hG : G.Preconnected) (v₀ : V)
    (hδ : δ ⊆ G.edgeFinset) :
    disagree G (parityProp G δ hG v₀) = δ := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    constructor
    · 
      intro he
      have hadj : G.Adj x y := by
        have := disagree_subset_edgeFinset (parityProp G δ hG v₀) he
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
      have hne : (parityProp G δ hG v₀) x ≠ (parityProp G δ hG v₀) y :=
        (mem_disagree_iff (parityProp G δ hG v₀) hadj).mp he
      have hxor : (parityProp G δ hG v₀ x).xor (parityProp G δ hG v₀ y) = true := by
        cases hx : parityProp G δ hG v₀ x <;> cases hy : parityProp G δ hG v₀ y <;>
          simp_all
      rw [parityProp_adj_xor hev hG v₀ hadj] at hxor
      exact of_decide_eq_true hxor
    · 
      intro he
      have hadj : G.Adj x y := by
        have := hδ he
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
      rw [mem_disagree_iff (parityProp G δ hG v₀) hadj]
      have hxor := parityProp_adj_xor hev hG v₀ hadj
      rw [decide_eq_true he] at hxor
      cases hx : parityProp G δ hG v₀ x <;> cases hy : parityProp G δ hG v₀ y <;>
        simp_all


theorem exists_disagree_eq_of_evenOnAllCycles [Nonempty V] (hG : G.Preconnected)
    (hδ : δ ⊆ G.edgeFinset) (hev : EvenOnAllCycles G δ) :
    ∃ c : V → Bool, disagree G c = δ := by
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
  exact ⟨parityProp G δ hG v₀, disagree_parityProp hev hG v₀ hδ⟩


theorem evenOnAllCycles_iff_exists_disagree [Nonempty V] (hG : G.Preconnected)
    (hδ : δ ⊆ G.edgeFinset) :
    EvenOnAllCycles G δ ↔ ∃ c : V → Bool, disagree G c = δ := by
  constructor
  · intro hev; exact exists_disagree_eq_of_evenOnAllCycles hG hδ hev
  · rintro ⟨c, rfl⟩; exact disagree_evenOnAllCycles c

end ParityProp
end StatMech.Walls
