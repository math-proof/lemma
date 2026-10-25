/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part5
import Def.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section ParityConfig

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp : SimpleGraph V) [DecidableRel Gp.Adj] (δ : Finset (Sym2 V))


variable {Gp δ}

omit [Fintype V] [DecidableRel Gp.Adj] in


theorem parityConfig_adj_xor (hev : EvenOnCycles Gp δ) (hG : Gp.Preconnected) (v₀ : V)
    {x y : V} (h : Gp.Adj x y) :
    (parityConfig Gp δ hG v₀ x).xor (parityConfig Gp δ hG v₀ y) = decide (s(x, y) ∈ δ) := by
  
  let px : Gp.Walk v₀ x := (hG v₀ x).some
  let walkVy : Gp.Walk v₀ y := px.append (SimpleGraph.Walk.cons h (.nil : Gp.Walk y y))
  have hpar : parityConfig Gp δ hG v₀ y = walkParity Gp δ walkVy := by
    unfold parityConfig
    exact walkParity_eq_of_evenOnCycles hev (hG v₀ y).some walkVy
  have hwalkVy : walkParity Gp δ walkVy
      = (parityConfig Gp δ hG v₀ x).xor (decide (s(x, y) ∈ δ)) := by
    rw [walkParity_append, walkParity_singleton]
    rfl
  rw [hpar, hwalkVy]
  
  cases parityConfig Gp δ hG v₀ x <;>
    cases hb : decide (s(x, y) ∈ δ) <;> simp


theorem cutEdges_parityConfig (hev : EvenOnCycles Gp δ) (hG : Gp.Preconnected) (v₀ : V)
    (hδ : δ ⊆ Gp.edgeFinset) :
    cutEdges Gp (parityConfig Gp δ hG v₀) = δ := by
  classical
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    constructor
    · 
      intro he
      have hadj : Gp.Adj x y := by
        rw [cutEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        exact he.1
      have hne : (parityConfig Gp δ hG v₀) x ≠ (parityConfig Gp δ hG v₀) y :=
        (mem_cutEdges_iff Gp _ hadj).mp he
      
      have hxor : (parityConfig Gp δ hG v₀ x).xor (parityConfig Gp δ hG v₀ y) = true := by
        cases hx : parityConfig Gp δ hG v₀ x <;> cases hy : parityConfig Gp δ hG v₀ y <;>
          simp_all
      rw [parityConfig_adj_xor hev hG v₀ hadj] at hxor
      exact of_decide_eq_true hxor
    · 
      intro he
      have hadj : Gp.Adj x y := by
        have := hδ he
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
      rw [mem_cutEdges_iff Gp _ hadj]
      have hxor := parityConfig_adj_xor hev hG v₀ hadj
      rw [decide_eq_true (by exact he)] at hxor
      
      cases hx : parityConfig Gp δ hG v₀ x <;> cases hy : parityConfig Gp δ hG v₀ y <;>
        simp_all


theorem mem_cutSpace_of_evenOnCycles [Nonempty V] (hG : Gp.Preconnected)
    (hδ : δ ⊆ Gp.edgeFinset) (hev : EvenOnCycles Gp δ) :
    δ ∈ cutSpace Gp := by
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
  rw [cutSpace, Finset.mem_image]
  exact ⟨parityConfig Gp δ hG v₀, Finset.mem_univ _, cutEdges_parityConfig hev hG v₀ hδ⟩

end ParityConfig
end Ising
end StatMech
