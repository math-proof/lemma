/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/GraphMinor.lean -/

/-
# Finite graphs and the graph-minor relation
-/

import Mathlib.Combinatorics.SimpleGraph.Maps
import Inductive.Combinatorics.Graph.GraphMinor


namespace MetaMathlibExt

/-- Graph-minor relation: `H` is a minor of `G` if `H` is obtainable from `G`
by a sequence of isomorphisms, single-vertex deletions, single-edge deletions,
and single-edge contractions.
Stable source: https://en.wikipedia.org/wiki/Robertson%E2%80%93Seymour_theorem. -/
def IsMinor (H G : FinGraph) : Prop :=
  Relation.ReflTransGen MinorStep H G

end MetaMathlibExt
