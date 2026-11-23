/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.Chain
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Theorem.Combinatorics.RoadColoring.Part2

@[expose] public section

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

noncomputable def rc_level {V : Type*} [Finite V] (g : V → V) (v : V) : ℕ := by
  classical
  have : Fintype V := Fintype.ofFinite V
  exact Nat.find (p := fun i => g^[i] v ∈ Function.periodicPts g)
    (rc_level_exists g v)

noncomputable def rc_root {V : Type*} [Finite V] (g : V → V) (v : V) : V :=
  g^[rc_level g v] v

end RoadColoring
end
end MetaMathlibExt
