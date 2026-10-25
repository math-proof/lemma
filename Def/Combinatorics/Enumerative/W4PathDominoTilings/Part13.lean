/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.W4PathDominoTilings.Part10
open SimpleGraph


section

namespace MetaMathlibExt

noncomputable def bwdTiling (m : ℕ) (t : Tiling m ∅) :
    { M : (W4 □ pathGraph m).Subgraph // M.IsPerfectMatching } :=
  ⟨bwdSubgraph m t, bwdSubgraph_perfect m t⟩

end MetaMathlibExt
end
