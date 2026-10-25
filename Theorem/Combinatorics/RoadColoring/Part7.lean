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
import Def.Combinatorics.RoadColoring.Part7
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

theorem rc_height_gt_of_iterate_notMem {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V) (v : V) (L : ℕ) (h : g^[L] v ∉ Function.periodicPts g) :
    L < rc_height g := by
  by_contra hcon
  have h1 := rc_level_le_height g v
  have h2 : rc_height g ≤ L := by omega
  have hle : rc_level g v ≤ L := le_trans h1 h2
  exact h (rc_iterate_ge_level_periodic g v hle)

theorem rc_path_point_notMem {V : Type*} [Finite V] (R : V → V) (p : V)
    {i : ℕ} (hi : i < rc_level R p) : R^[i] p ∉ Function.periodicPts R := by
  intro hmem
  have h0 : rc_level R (R^[i] p) = 0 := (rc_level_zero_iff R _).mpr hmem
  have hlev := rc_level_along_orbit R p i (by omega)
  omega

theorem rc_root_of_mem_orbit {V : Type*} [Finite V] (R : V → V) (v x : V)
    (hmem : ∃ i : ℕ, R^[i] v = x) (hxnp : x ∉ Function.periodicPts R) :
    rc_root R x = rc_root R v := by
  obtain ⟨i, hi⟩ := hmem
  have hiL : i ≤ rc_level R v := by
    by_contra hcon
    have hle : rc_level R v ≤ i := by omega
    have h := rc_iterate_ge_level_periodic R v hle
    rw [hi] at h
    exact hxnp h
  have hroot := rc_root_along_orbit R v hiL
  rw [hi] at hroot
  exact hroot

theorem rc_orbit_avoid_of_root_ne {V : Type*} [Finite V] (R : V → V) (v x : V)
    (hxnp : x ∉ Function.periodicPts R) (hne : rc_root R v ≠ rc_root R x) (i : ℕ) :
    R^[i] v ≠ x :=
  fun heq => hne (rc_root_of_mem_orbit R v x ⟨i, heq⟩ hxnp).symm

end RoadColoring
end
end MetaMathlibExt
