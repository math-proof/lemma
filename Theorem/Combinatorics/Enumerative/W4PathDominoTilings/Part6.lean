module
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Nat.Fib.Basic
public import Def.NumberTheory.PellNumberSequence
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.W4PathDominoTilings.Part8
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/
section

namespace MetaMathlibExt

theorem vertSet_top_empty (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : m ≤ j + 1) :
    vertSet m M hM j = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro a hmem
  rw [vertSet_mem] at hmem
  obtain ⟨i, k, hi, hk, -⟩ := hmem
  have hlt : k.val < m := k.isLt
  omega

end MetaMathlibExt
end
