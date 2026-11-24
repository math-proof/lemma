module
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Nat.Fib.Basic
public import Def.NumberTheory.PellNumberSequence
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.W4PathDominoTilings.Part6
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/
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
