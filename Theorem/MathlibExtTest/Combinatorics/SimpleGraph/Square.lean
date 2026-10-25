/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Square.lean -/


import Mathlib.Combinatorics.SimpleGraph.Hasse
import Theorem.Combinatorics.SimpleGraph.Square
import Lemma.SimpleGraph.Square


namespace MathlibExtTest.Combinatorics.SimpleGraph.Square

example : (SimpleGraph.pathGraph 3).square.Adj 0 2 :=
  path_square_adj_zero_two

example : (⊤ : SimpleGraph (Fin 3)).square.Adj 0 2 := by
  apply SimpleGraph.square_mono (G := SimpleGraph.pathGraph 3)
    (H := (⊤ : SimpleGraph (Fin 3))) (by simp)
  exact path_square_adj_zero_two

example : (SimpleGraph.pathGraph 3).square.Reachable 0 2 := by
  exact (SimpleGraph.pathGraph_connected 2).square 0 2

example : (⊤ : SimpleGraph (Fin 3)).square.IsHamiltonian := by
  apply SimpleGraph.IsHamiltonian.square_mono
    (G := SimpleGraph.pathGraph 3) (H := (⊤ : SimpleGraph (Fin 3))) (by simp)
  exact path_square_isHamiltonian

example : (SimpleGraph.pathGraph 3).square = ⊤ := by
  classical
  symm
  apply SimpleGraph.eq_square_iff.mpr
  intro u v
  fin_cases u <;> fin_cases v <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk,
      SimpleGraph.top_adj, SimpleGraph.irrefl, ne_eq, Fin.reduceEq,
      not_false_eq_true, not_true_eq_false, SimpleGraph.pathGraph_adj,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.one_mod, Nat.mod_succ, zero_add,
      Nat.reduceAdd, Nat.add_eq_zero_iff, Nat.add_eq_right, Fin.val_eq_zero_iff,
      one_ne_zero, zero_ne_one, OfNat.ofNat_ne_zero, OfNat.one_ne_ofNat,
      OfNat.ofNat_ne_one, Nat.reduceEqDiff, or_false, false_or, true_or, or_true,
      or_self, and_false, false_and, and_true, true_and, and_self, exists_or_eq_imp,
      true_iff]
  all_goals exact ⟨1, by simp⟩

example : List.IsChain (SimpleGraph.pathGraph 3).square.Adj [0, 2] := by
  apply SimpleGraph.isChain_square_of_isChain_cons_cons (w := (1 : Fin 3)) (l := [])
  · rw [List.isChain_cons_cons, List.isChain_pair]
    exact ⟨SimpleGraph.pathGraph_adj.mpr (Or.inl rfl),
      SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)⟩
  · decide

end MathlibExtTest.Combinatorics.SimpleGraph.Square
