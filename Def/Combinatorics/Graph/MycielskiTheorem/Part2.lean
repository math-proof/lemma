/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.CharP.Defs
import Mathlib.Order.CompletePartialOrder
import Theorem.Combinatorics.Graph.MycielskiTheorem


namespace MetaMathlibExt

open scoped SimpleGraph

def myGraph {V : Type*} (G : SimpleGraph V) : SimpleGraph (Option (V × Bool)) where
  Adj := myAdj G
  symm := myAdj_symm G
  loopless := myAdj_irrefl G

end MetaMathlibExt
