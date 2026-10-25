/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.CharP.Defs
import Mathlib.Order.CompletePartialOrder
import Def.Combinatorics.Graph.MycielskiTheorem.Part2


namespace MetaMathlibExt

open scoped SimpleGraph

theorem myAdj_of00 {V : Type*} {G : SimpleGraph V} {v u : V} (h : G.Adj v u) :
    myAdj G (some (v, false)) (some (u, false)) :=
  Or.inl ⟨v, u, rfl, rfl, h⟩

end MetaMathlibExt
