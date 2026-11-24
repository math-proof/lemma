module
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Nat.Fib.Basic
public import Def.NumberTheory.PellNumberSequence
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.W4PathDominoTilings.Part12
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/
section

namespace MetaMathlibExt

theorem bwdSubgraph_perfect (m : ℕ) (t : Tiling m ∅) :
    (bwdSubgraph m t).IsPerfectMatching := by
  rw [Subgraph.isPerfectMatching_iff]
  intro v
  exact ⟨partnerT m t v, rfl, fun w hw => hw⟩

end MetaMathlibExt
end
