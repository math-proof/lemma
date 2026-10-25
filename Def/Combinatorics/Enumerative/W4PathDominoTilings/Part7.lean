/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.W4PathDominoTilings.Part4
open SimpleGraph


section

namespace MetaMathlibExt

noncomputable def belowSet (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) : ℕ → Finset (Fin 4)
  | 0 => ∅
  | (j + 1) => vertSet m M hM j

noncomputable def aboveSet (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) : Finset (Fin 4) :=
  vertSet m M hM j

noncomputable def leftoverSet (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) : Finset (Fin 4) :=
  Finset.univ \ (belowSet m M hM j ∪ aboveSet m M hM j)

end MetaMathlibExt
end
