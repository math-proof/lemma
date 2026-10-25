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
import Theorem.Combinatorics.RoadColoring.Part4
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

def rc_stableSetoid {V : Type*} {k : ℕ} (delta : V → Fin k → V) : Setoid V where
  r := rc_stable delta
  iseqv := ⟨rc_stable_refl delta, fun h => rc_stable_symm delta h,
    fun h1 h2 => rc_stable_trans delta h1 h2⟩

def rc_quot {V : Type*} {k : ℕ} (delta : V → Fin k → V) :
    Quotient (rc_stableSetoid delta) → Fin k → Quotient (rc_stableSetoid delta) :=
  fun q c => Quotient.map' (fun v => delta v c)
    (fun _v _w h => rc_stable_foldl delta h [c]) q

end RoadColoring
end
end MetaMathlibExt
