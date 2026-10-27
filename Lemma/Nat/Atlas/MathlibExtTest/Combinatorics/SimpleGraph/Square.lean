import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.Square.Part2


namespace MathlibExtTest.Combinatorics.SimpleGraph.Square

/--
[path_square_adj_zero_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Square.lean)
-/
@[path]
private lemma path_square_adj_zero_two :
  (SimpleGraph.pathGraph 3).square.Adj 0 2 := by
  rw [SimpleGraph.square_adj]
  exact ⟨by decide, Or.inr ⟨1,
    SimpleGraph.pathGraph_adj.mpr (Or.inl rfl),
    SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)⟩⟩

end MathlibExtTest.Combinatorics.SimpleGraph.Square

namespace MathlibExtTest.Combinatorics.SimpleGraph.Square

/--
[path_square_isHamiltonian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Square.lean)
-/
@[path]
private lemma path_square_isHamiltonian :
  (SimpleGraph.pathGraph 3).square.IsHamiltonian := by
  apply SimpleGraph.IsHamiltonian.square_of_cyclic_list (SimpleGraph.pathGraph 3)
    [0, 1, 2, 0] (by decide)
  · decide
  · rw [List.isChain_cons_cons, List.isChain_cons_cons, List.isChain_pair]
    constructor
    · exact ⟨by decide, Or.inl (SimpleGraph.pathGraph_adj.mpr (Or.inl rfl))⟩
    constructor
    · exact ⟨by decide, Or.inl (SimpleGraph.pathGraph_adj.mpr (Or.inl rfl))⟩
    exact ⟨by decide, Or.inr ⟨1, SimpleGraph.pathGraph_adj.mpr (Or.inr rfl),
      SimpleGraph.pathGraph_adj.mpr (Or.inr rfl)⟩⟩
  · decide
  · decide
  · decide

end MathlibExtTest.Combinatorics.SimpleGraph.Square

/--
[completeGraph_isVertexConnected_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Square.lean)
-/
@[path]
private lemma completeGraph_isVertexConnected_two :
  SimpleGraph.IsVertexConnected 2 (⊤ : SimpleGraph (Fin 5)) := by
  rw [SimpleGraph.isVertexConnected_two_iff]
  refine ⟨by decide, SimpleGraph.connected_top, ?_⟩
  intro v
  rw [SimpleGraph.induce_top]
  let _ : Nonempty {x : Fin 5 // x ∈ (↑({v} : Finset (Fin 5)) : Set (Fin 5))ᶜ} :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_compl_set]
      simp)
  exact SimpleGraph.connected_top



-- created on 2026-10-23
