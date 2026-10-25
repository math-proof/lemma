/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.W4PathDominoTilings.Part6
open SimpleGraph


section

namespace MetaMathlibExt

theorem pathGraph_irrefl (m : ℕ) (i : Fin m) : ¬(pathGraph m).Adj i i := by
  rw [pathGraph_adj]
  omega

theorem partner_same_layer_horiz (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (a : Fin 4) (i : Fin m)
    (h : (partner m M hM (a, i)).2 = i) : W4.Adj a (partner m M hM (a, i)).1 := by
  have hc := partner_classify m M hM a i
  simp only at hc
  rcases hc with ⟨hW, -⟩ | ⟨hpath, -⟩
  · exact hW
  · rw [h] at hpath
    exact absurd hpath (pathGraph_irrefl m i)

theorem partner_ne_layer_vert (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (a : Fin 4) (i : Fin m)
    (h : (partner m M hM (a, i)).2 ≠ i) :
    (partner m M hM (a, i)).1 = a ∧ (pathGraph m).Adj i (partner m M hM (a, i)).2 := by
  have hc := partner_classify m M hM a i
  simp only at hc
  rcases hc with ⟨-, heq⟩ | ⟨hpath, haeq⟩
  · exact absurd heq.symm h
  · exact ⟨haeq.symm, hpath⟩

end MetaMathlibExt
end
