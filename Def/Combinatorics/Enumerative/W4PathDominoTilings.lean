/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
open SimpleGraph


section

namespace MetaMathlibExt

/-! # Domino tilings and Fibonacci–Pell products
-/

-- Pell helpers (closed-form side): same pair recurrence as in the statement.
def pellPair : ℕ → ℕ × ℕ :=
  Nat.rec (motive := fun (_ : ℕ) => ℕ × ℕ) (0, 1)
    (fun (_ : ℕ) (ih : ℕ × ℕ) => (ih.2, 2 * ih.2 + ih.1))

def pell (n : ℕ) : ℕ := (pellPair n).1

-- d m = fib (m + 1) * pell (m + 1): closed form with n = m + 1.
def dval (m : ℕ) : ℕ := Nat.fib (m + 1) * pell (m + 1)

-- Counting side setup: W_4 is K_4 minus the edge {0, 1}.
def W4 : SimpleGraph (Fin 4) :=
  (SimpleGraph.completeGraph (Fin 4)).deleteEdges {Sym2.mk (0 : Fin 4) (1 : Fin 4)}

end MetaMathlibExt
end
