/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.W4PathDominoTilings.Part12
open SimpleGraph


section

namespace MetaMathlibExt

theorem bwdSubgraph_perfect (m : ℕ) (t : Tiling m ∅) :
    (bwdSubgraph m t).IsPerfectMatching := by
  rw [Subgraph.isPerfectMatching_iff]
  intro v
  exact ⟨partnerT m t v, rfl, fun w hw => hw⟩

end MetaMathlibExt
end
