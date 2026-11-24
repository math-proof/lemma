module
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Nat.Fib.Basic
public import Def.NumberTheory.PellNumberSequence
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.W4PathDominoTilings.Part2
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/
section

namespace MetaMathlibExt

-- Vertical edges at boundary `j` (between layers `j` and `j+1`), seen from below.
noncomputable def vertSet (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) : Finset (Fin 4) :=
  Finset.univ.filter (fun a =>
    ∃ i k : Fin m, i.val = j ∧ k.val = j + 1 ∧ partner m M hM (a, i) = (a, k))

end MetaMathlibExt
end
