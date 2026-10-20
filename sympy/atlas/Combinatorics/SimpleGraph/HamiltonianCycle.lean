/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HamiltonianCycle.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Hamiltonian cycles from cyclic listings

This file turns a cyclic listing of all vertices into a Hamiltonian cycle.
-/

namespace SimpleGraph

/-- A closed, nonrepeating cyclic listing of every vertex witnesses a Hamiltonian graph. -/
theorem IsHamiltonian.of_cyclic_list {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (l : List V) (hne : l ≠ [])
    (hclosed : l.head hne = l.getLast hne) (hchain : l.IsChain G.Adj)
    (hnodup : l.tail.Nodup) (hmem : ∀ v, v ∈ l.tail)
    (hthree : 3 ≤ l.length - 1) : G.IsHamiltonian := by
  let q := Walk.ofSupport l hne hchain
  let p : G.Walk (l.head hne) (l.head hne) := q.copy rfl hclosed.symm
  have hp_length : p.length = l.length - 1 := by
    simp only [p, q, Walk.length_copy, Walk.length_ofSupport]
  have hp_not_nil : ¬p.Nil := by
    rw [Walk.not_nil_iff_lt_length, hp_length]
    omega
  have hp_support : p.support = l := by
    simp only [p, q, Walk.support_copy, Walk.support_ofSupport]
  have hp_cycle : p.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    constructor
    · rw [Walk.isPath_def, p.support_tail_of_not_nil hp_not_nil, hp_support]
      exact hnodup
    · omega
  intro _
  refine ⟨l.head hne, p, Walk.IsHamiltonianCycle.mk hp_cycle ?_⟩
  apply hp_cycle.isPath_tail.isHamiltonian_of_mem
  intro v
  rw [p.support_tail_of_not_nil hp_not_nil, hp_support]
  exact hmem v

end SimpleGraph
