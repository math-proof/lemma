/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean -/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Order.CompletePartialOrder
public import Theorem.Combinatorics.Graph.MycielskiTheorem

@[expose] public section

namespace MetaMathlibExt

open scoped SimpleGraph

def myGraph {V : Type*} (G : SimpleGraph V) : SimpleGraph (Option (V × Bool)) where
  Adj := myAdj G
  symm := myAdj_symm G
  loopless := myAdj_irrefl G

end MetaMathlibExt
