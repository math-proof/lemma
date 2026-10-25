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

def rc_adj {V : Type*} {k : ℕ} (delta : V → Fin k → V) (v w : V) : Prop :=
  ∃ a : Fin k, delta v a = w

def rc_recolor {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    (sigma : V → Equiv.Perm (Fin k)) : V → Fin k → V :=
  fun v a => delta v (sigma v a)

def rc_sync {V : Type*} {k : ℕ} (delta : V → Fin k → V) : Prop :=
  ∃ (word : List (Fin k)) (r : V), ∀ v : V, List.foldl delta v word = r

def rc_strongly {V : Type*} {k : ℕ} (delta : V → Fin k → V) : Prop :=
  ∀ u v : V, Relation.ReflTransGen (rc_adj delta) u v

def rc_aperiodic {V : Type*} {k : ℕ} (delta : V → Fin k → V) : Prop :=
  ∀ d : ℕ, 1 < d → ∃ (u : V) (w : List V),
    List.IsChain (rc_adj delta) (u :: w) ∧ w.getLast? = some u ∧ ¬ (d ∣ w.length)

def rc_stable {V : Type*} {k : ℕ} (delta : V → Fin k → V) (p q : V) : Prop :=
  ∀ u : List (Fin k), ∃ v : List (Fin k),
    List.foldl delta p (u ++ v) = List.foldl delta q (u ++ v)

end RoadColoring
end
end MetaMathlibExt
