/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Chain
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Theorem.Combinatorics.RoadColoring.Part3
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

noncomputable def rc_height {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V) : ℕ :=
  Finset.sup Finset.univ (fun v => rc_level g v)

noncomputable def rc_cyc {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun v => v ∈ Function.periodicPts g)).card

def rc_good {V : Type*} [Fintype V] [DecidableEq V] (g : V → V) : Prop :=
  0 < rc_height g ∧ ∀ v w : V, rc_level g v = rc_height g →
    rc_level g w = rc_height g → rc_root g v = rc_root g w

end RoadColoring
end
end MetaMathlibExt
