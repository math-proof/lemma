/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/GraphMinor.lean -/

/-
# Finite graphs and the graph-minor relation
-/

import Mathlib.Combinatorics.SimpleGraph.Maps


namespace MetaMathlibExt

/-- Bundled finite simple graph: a vertex type together with its finiteness
witness and a simple graph on it. The witness is an instance-implicit field,
so it is synthesized by typeclass search at construction; downstream code
still accesses it explicitly as `G.fin`, since instances cannot depend on a
locally bound graph.
Stable source: https://en.wikipedia.org/wiki/Robertson%E2%80%93Seymour_theorem. -/
structure FinGraph where
  V : Type*
  [fin : Finite V]
  G : SimpleGraph V

end MetaMathlibExt
