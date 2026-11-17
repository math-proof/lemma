/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean -/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Order.CompletePartialOrder
public import Def.Combinatorics.Graph.MycielskiTheorem.Part2

public section

namespace MetaMathlibExt

open scoped SimpleGraph

theorem myAdj_of00 {V : Type*} {G : SimpleGraph V} {v u : V} (h : G.Adj v u) :
    myAdj G (some (v, false)) (some (u, false)) :=
  Or.inl ⟨v, u, rfl, rfl, h⟩

end MetaMathlibExt
