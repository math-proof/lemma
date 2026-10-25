/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.CharP.Defs
import Mathlib.Order.CompletePartialOrder


namespace MetaMathlibExt

open scoped SimpleGraph

def myAdj {V : Type*} (G : SimpleGraph V) : Option (V × Bool) → Option (V × Bool) → Prop :=
  fun x y =>
    (∃ v u, x = some (v, false) ∧ y = some (u, false) ∧ G.Adj v u) ∨
    (∃ v u, x = some (v, false) ∧ y = some (u, true) ∧ G.Adj v u) ∨
    (∃ v u, x = some (v, true) ∧ y = some (u, false) ∧ G.Adj v u) ∨
    (∃ v, x = some (v, true) ∧ y = none) ∨
    (∃ v, x = none ∧ y = some (v, true))

end MetaMathlibExt
