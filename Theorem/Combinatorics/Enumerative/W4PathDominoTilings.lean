/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/
module

public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Nat.Fib.Basic
public import Def.NumberTheory.PellNumberSequence
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.W4PathDominoTilings
open SimpleGraph

public section

section

namespace MetaMathlibExt

theorem W4_adj (a b : Fin 4) :
    W4.Adj a b ↔ a ≠ b ∧ s(a, b) ≠ s((0 : Fin 4), (1 : Fin 4)) := by
  unfold W4
  rw [deleteEdges_adj, completeGraph_eq_top, top_adj]
  constructor
  · rintro ⟨hne, hmem⟩
    refine ⟨hne, ?_⟩
    simpa using hmem
  · rintro ⟨hne, hne2⟩
    refine ⟨hne, ?_⟩
    simpa using hne2

end MetaMathlibExt
end
