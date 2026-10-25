/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/CliqueNumber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Theorem.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter4.CliqueNumber
set_option maxHeartbeats 400000

open scoped Classical
open Finset BigOperators Filter Topology


namespace CliqueNumber

/-- Equivalence decomposing a Boolean algebra $\alpha$ as the product
    $[\bot, a] \times [\bot, a^c]$ via the map $x \mapsto (x \sqcap a, x \sqcap a^c)$. -/
noncomputable def boolAlgDecomp {α : Type*} [BooleanAlgebra α] (a : α) :
    α ≃ Set.Iic a × Set.Iic aᶜ where
  toFun x := ⟨⟨x ⊓ a, inf_le_right⟩, ⟨x ⊓ aᶜ, inf_le_right⟩⟩
  invFun p := (p.1 : α) ⊔ (p.2 : α)
  left_inv x := by
    show x ⊓ a ⊔ x ⊓ aᶜ = x
    rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq]
  right_inv p := by
    ext
    · exact ba_sup_inf_right p.1.2 p.2.2
    · exact ba_sup_inf_compl p.1.2 p.2.2

/-- Equivalence between the upper set $[a, \top]$ and the lower set $[\bot, a^c]$
    in a Boolean algebra, given by complementation. -/
noncomputable def iciEquivIicCompl {α : Type*} [BooleanAlgebra α] (a : α) :
    Set.Ici a ≃ Set.Iic aᶜ where
  toFun x := ⟨(x : α)ᶜ, compl_le_compl x.2⟩
  invFun y := ⟨(y : α)ᶜ, compl_le_compl_iff_le.mp (by rw [compl_compl]; exact y.2)⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

/-- Equivalence between subgraphs of a simple graph $a$ on $V$ and Boolean functions on its
    edge set: a subgraph corresponds to the indicator on whether each edge is kept. -/
noncomputable def iicEquivBoolFn {V : Type*} [Fintype V] [DecidableEq V]
    (a : SimpleGraph V) : Set.Iic a ≃ (↥(a.edgeFinset) → Bool) where
  toFun G e := decide ((e : Sym2 V) ∈ (G : SimpleGraph V).edgeSet)
  invFun f := ⟨SimpleGraph.fromEdgeSet
    {e : Sym2 V | ∃ h : e ∈ a.edgeFinset, f ⟨e, h⟩ = true}, by
    simp only [Set.mem_Iic, ← SimpleGraph.edgeSet_subset_edgeSet,
      SimpleGraph.edgeSet_fromEdgeSet]
    intro e he
    simp only [Set.mem_diff, Set.mem_setOf_eq] at he
    exact SimpleGraph.mem_edgeFinset.mp he.1.choose⟩
  left_inv G := by
    ext v w
    change (SimpleGraph.fromEdgeSet _).Adj v w ↔ (G : SimpleGraph V).Adj v w
    rw [SimpleGraph.fromEdgeSet_adj]
    constructor
    · intro ⟨hset, _⟩
      simp only [Set.mem_setOf_eq] at hset
      obtain ⟨_, hf⟩ := hset
      rw [decide_eq_true_iff, SimpleGraph.mem_edgeSet] at hf; exact hf
    · intro hadj
      refine ⟨?_, (G : SimpleGraph V).ne_of_adj hadj⟩
      simp only [Set.mem_setOf_eq]
      exact ⟨SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.edgeSet_subset_edgeSet.mpr G.2 hadj),
             by rw [decide_eq_true_iff, SimpleGraph.mem_edgeSet]; exact hadj⟩
  right_inv f := by
    funext ⟨e, he⟩
    simp only [SimpleGraph.edgeSet_fromEdgeSet, Set.mem_diff, Set.mem_setOf_eq]
    have hnd : e ∉ Sym2.diagSet :=
      a.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he)
    simp only [hnd, not_false_eq_true, and_true]
    simp only [show (∃ h : e ∈ a.edgeFinset, f ⟨e, h⟩ = true) ↔ f ⟨e, he⟩ = true from
      ⟨fun ⟨_, hf⟩ => by convert hf, fun hf => ⟨he, hf⟩⟩]
    simp

end CliqueNumber
