/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.W4PathDominoTilings.Part5
open SimpleGraph


section

namespace MetaMathlibExt

theorem vertSet_mem (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (a : Fin 4) :
    a ∈ vertSet m M hM j ↔
      ∃ i k : Fin m, i.val = j ∧ k.val = j + 1 ∧ partner m M hM (a, i) = (a, k) := by
  unfold vertSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem partner_pair_symm (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (a : Fin 4) (i k : Fin m)
    (heq : partner m M hM (a, i) = (a, k)) :
    partner m M hM (a, k) = (a, i) := by
  have hps := partner_symm m M hM (a, i)
  rw [heq] at hps
  exact hps

end MetaMathlibExt
end
