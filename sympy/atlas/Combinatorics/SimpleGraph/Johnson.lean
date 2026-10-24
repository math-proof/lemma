/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Johnson.lean -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Card

/-!
# Johnson graphs

Adapted from
`google-deepmind/formal-conjectures@62f56e8e4dab933a720f649721875c478b0ecf1c`,
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Johnson.lean`.
-/

namespace SimpleGraph

/-- The Johnson graph `J(n, k)`: its vertices are the `k`-subsets of `Fin n`, and two
vertices are adjacent when their intersection has cardinality `k - 1`. -/
def johnsonGraph (n k : ℕ) : SimpleGraph {s : Finset (Fin n) // s.card = k} where
  Adj s t := (s.val ∩ t.val).card + 1 = k
  symm.symm s t h := by simpa [Finset.inter_comm]
  loopless.irrefl := by simp +contextual
end SimpleGraph
