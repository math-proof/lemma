/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.W4PathDominoTilings.Part8
open SimpleGraph


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
