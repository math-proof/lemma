/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Instance.Combinatorics.Enumerative.W4PathDominoTilings.Part3
open SimpleGraph


section

namespace MetaMathlibExt

def Ncount (m : ℕ) (S : Finset (Fin 4)) : ℕ := Fintype.card (Tiling m S)

-- Five aggregated boundary states.
def Aval (m : ℕ) : ℕ := Ncount m ∅

def Bval (m : ℕ) : ℕ :=
  Ncount m {0, 2} + Ncount m {0, 3} + Ncount m {1, 2} + Ncount m {1, 3}

def Cval (m : ℕ) : ℕ := Ncount m {2, 3}

def Dval (m : ℕ) : ℕ := Ncount m {0, 1}

def Eval (m : ℕ) : ℕ := Ncount m Finset.univ

-- Partner function of a perfect matching.
noncomputable def partner (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) : Fin 4 × Fin m → Fin 4 × Fin m :=
  fun v => Classical.choose ((Subgraph.isPerfectMatching_iff.mp hM v).exists)

end MetaMathlibExt
end
