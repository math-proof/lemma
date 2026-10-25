/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.W4PathDominoTilings.Part2
open SimpleGraph


section

namespace MetaMathlibExt

-- Vertical edges at boundary `j` (between layers `j` and `j+1`), seen from below.
noncomputable def vertSet (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) : Finset (Fin 4) :=
  Finset.univ.filter (fun a =>
    ∃ i k : Fin m, i.val = j ∧ k.val = j + 1 ∧ partner m M hM (a, i) = (a, k))

end MetaMathlibExt
end
