import Mathlib
import sympy.Basic


namespace SimpleGraph

/--
[IsHamiltonian.of_cyclic_list](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HamiltonianCycle.lean)
-/
@[path]
lemma IsHamiltonian.of_cyclic_list
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}
  {l : List V}
-- given
  (hne : l ≠ [])
  (hclosed : l.head hne = l.getLast hne)
  (hchain : l.IsChain G.Adj)
  (hnodup : l.tail.Nodup)
  (hmem : ∀ v, v ∈ l.tail)
  (hthree : 3 ≤ l.length - 1) :
-- imply
  G.IsHamiltonian := by
-- proof
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


-- created on 2026-10-20
-- updated on 2026-10-23
