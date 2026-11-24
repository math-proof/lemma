module
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Nat.Fib.Basic
public import Def.NumberTheory.PellNumberSequence
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.W4PathDominoTilings.Part9
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/
section

namespace MetaMathlibExt

noncomputable def bwdSubgraph (m : ℕ) (t : Tiling m ∅) :
    (W4 □ pathGraph m).Subgraph where
  verts := Set.univ
  Adj v w := w = partnerT m t v
  adj_sub h := by
    rw [h]
    exact partnerT_adj _ _ _
  edge_vert _ := Set.mem_univ _
  symm := ⟨fun {v w} h => by
    have hinv := partnerT_involutive m t v
    have h2 : partnerT m t w = v := by
      rw [h]
      exact hinv
    exact h2.symm⟩

end MetaMathlibExt
end
