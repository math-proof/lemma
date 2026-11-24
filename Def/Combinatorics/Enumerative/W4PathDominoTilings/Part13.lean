module
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Nat.Fib.Basic
public import Def.NumberTheory.PellNumberSequence
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.W4PathDominoTilings.Part10
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/
section

namespace MetaMathlibExt

noncomputable def bwdTiling (m : ℕ) (t : Tiling m ∅) :
    { M : (W4 □ pathGraph m).Subgraph // M.IsPerfectMatching } :=
  ⟨bwdSubgraph m t, bwdSubgraph_perfect m t⟩

end MetaMathlibExt
end
