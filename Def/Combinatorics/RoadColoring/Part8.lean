module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.Chain
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Theorem.Combinatorics.RoadColoring.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
/-!
# Road coloring theorem

This file proves the road coloring theorem of A. N. Trahtman, "The road coloring problem",
Israel J. Math. 172 (2009) 51–60. The proof follows the reduction of Culik, Karhumäki and Kari:
a recoloring with a stable pair passes to a smaller quotient automaton, and synchronizing words
lift back. Stable pairs come from two bunches into one vertex, or else from Trahtman's lemma on
spanning subgraphs with a unique highest tree, via Kari's minimal-rank argument.
-/
namespace MetaMathlibExt

section

namespace RoadColoring

noncomputable def rc_cycleFin {V : Type*} [DecidableEq V]
    (R : V → V) (r : V) : Finset V :=
  (Finset.range (Function.minimalPeriod R r)).image (fun t => R^[t] r)

end RoadColoring
end
end MetaMathlibExt
