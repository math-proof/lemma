/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Johnson.lean -/


import Def.Combinatorics.SimpleGraph.Johnson
import Lemma.SimpleGraph.Johnson


namespace SimpleGraph

example (n k : ℕ) (s t : {s : Finset (Fin n) // s.card = k}) :
    (johnsonGraph n k).Adj s t ↔ (s.val ∩ t.val).card + 1 = k :=
  johnsonGraph_adj_iff n k s t

example : (johnsonGraph 2 1).Adj ⟨{0}, by simp⟩ ⟨{1}, by simp⟩ := by
  rw [johnsonGraph_adj_iff]
  decide

example (n k : ℕ) (s : {s : Finset (Fin n) // s.card = k}) :
    ¬(johnsonGraph n k).Adj s s := by
  rw [johnsonGraph_adj_iff, Finset.inter_self, s.property]
  omega

example : ¬(johnsonGraph 4 2).Adj ⟨{0, 1}, by simp⟩ ⟨{2, 3}, by simp⟩ := by
  rw [johnsonGraph_adj_iff]
  decide

end SimpleGraph
