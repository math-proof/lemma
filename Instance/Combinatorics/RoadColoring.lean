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
import Def.Combinatorics.RoadColoring.Part5
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

noncomputable instance rc_quotFintype {V : Type*} [Fintype V] {k : ℕ}
    (delta : V → Fin k → V) : Fintype (Quotient (rc_stableSetoid delta)) := by
  classical
  exact Quotient.fintype _

instance rc_quotNonempty {V : Type*} [Nonempty V] {k : ℕ}
    (delta : V → Fin k → V) : Nonempty (Quotient (rc_stableSetoid delta)) :=
  ⟨Quotient.mk _ (Classical.choice ‹Nonempty V›)⟩

end RoadColoring
end
end MetaMathlibExt
