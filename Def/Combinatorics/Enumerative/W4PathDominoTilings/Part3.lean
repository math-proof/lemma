/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Instance.Combinatorics.Enumerative.W4PathDominoTilings.Part2
open SimpleGraph


section

namespace MetaMathlibExt

-- Explicit weight table: w(∅) = 1, w(univ) = 2, w(pair) = edge indicator, else 0.
def wHoriz (U : Finset (Fin 4)) : ℕ :=
  if U = ∅ then 1
  else if U = Finset.univ then 2
  else if U.card = 2 then
    (if ∃ a b : Fin 4, U = {a, b} ∧ W4.Adj a b then 1 else 0)
  else 0

-- Tilings of `m` layers with outgoing holes `S`: recursive transfer-matrix type.
def Tiling : ℕ → Finset (Fin 4) → Type
  | 0, S => PLift (S = ∅)
  | (m + 1), S' =>
      Σ S : Finset (Fin 4),
        PLift (Disjoint S S') × Tiling m S × HorizPairing (Finset.univ \ (S ∪ S'))

end MetaMathlibExt
end
