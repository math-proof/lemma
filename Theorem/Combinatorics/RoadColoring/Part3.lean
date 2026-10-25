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
import Def.Combinatorics.RoadColoring.Part3
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

theorem rc_level_spec {V : Type*} [Finite V] (g : V → V) (v : V) :
    g^[rc_level g v] v ∈ Function.periodicPts g := by
  classical
  have : Fintype V := Fintype.ofFinite V
  unfold rc_level
  exact Nat.find_spec (p := fun i => g^[i] v ∈ Function.periodicPts g)
    (rc_level_exists g v)

theorem rc_level_notMem {V : Type*} [Finite V] (g : V → V) (v : V)
    {m : ℕ} (hm : m < rc_level g v) : g^[m] v ∉ Function.periodicPts g := by
  classical
  have : Fintype V := Fintype.ofFinite V
  unfold rc_level at hm
  exact Nat.find_min (p := fun i => g^[i] v ∈ Function.periodicPts g)
    (rc_level_exists g v) hm

theorem rc_level_le_of_mem {V : Type*} [Finite V] (g : V → V) (v : V)
    {i : ℕ} (hi : g^[i] v ∈ Function.periodicPts g) :
    rc_level g v ≤ i := by
  classical
  have : Fintype V := Fintype.ofFinite V
  unfold rc_level
  exact Nat.find_min' (p := fun i => g^[i] v ∈ Function.periodicPts g)
    (rc_level_exists g v) hi

theorem rc_level_step {V : Type*} [Finite V] (g : V → V) (v : V)
    (hv : v ∉ Function.periodicPts g) :
    rc_level g (g v) = rc_level g v - 1 := by
  classical
  have hLpos : 0 < rc_level g v := by
    by_contra hcon
    have h0 : rc_level g v = 0 := by omega
    rw [rc_level_zero_iff] at h0
    exact hv h0
  have hL : 1 ≤ rc_level g v := hLpos
  have hdecomp : rc_level g v - 1 + 1 = rc_level g v := by omega
  have hmem : g^[rc_level g v - 1] (g v) ∈ Function.periodicPts g := by
    have hspec := rc_level_spec g v
    rw [← hdecomp, rc_iterate_succ_right] at hspec
    exact hspec
  have hle : rc_level g (g v) ≤ rc_level g v - 1 :=
    rc_level_le_of_mem g (g v) hmem
  have hge : rc_level g v - 1 ≤ rc_level g (g v) := by
    by_contra hcon
    have hlt : rc_level g (g v) < rc_level g v - 1 := by omega
    have hnot := rc_level_notMem g v
      (m := rc_level g (g v) + 1) (by omega)
    have heq : g^[rc_level g (g v) + 1] v =
        g^[rc_level g (g v)] (g v) := by
      rw [show rc_level g (g v) + 1 = rc_level g (g v) + 1 from rfl]
      exact (rc_iterate_succ_right g (rc_level g (g v)) v).symm
    rw [heq] at hnot
    exact hnot (rc_level_spec g (g v))
  omega

theorem rc_root_step {V : Type*} [Finite V] (g : V → V) (v : V)
    (hv : v ∉ Function.periodicPts g) :
    rc_root g (g v) = rc_root g v := by
  classical
  have hLpos : 0 < rc_level g v := by
    by_contra hcon
    have h0 : rc_level g v = 0 := by omega
    rw [rc_level_zero_iff] at h0
    exact hv h0
  have hdecomp : rc_level g v - 1 + 1 = rc_level g v := by omega
  unfold rc_root
  rw [rc_level_step g v hv]
  have hspec : g^[rc_level g v - 1] (g v) = g^[rc_level g v] v := by
    conv_rhs => rw [← hdecomp]
    exact (rc_iterate_succ_right g _ v).symm
  exact hspec

theorem rc_root_periodic {V : Type*} [Finite V] (g : V → V) (v : V) :
    rc_root g v ∈ Function.periodicPts g :=
  rc_level_spec g v

theorem rc_level_root_zero {V : Type*} [Finite V] (g : V → V) (v : V) :
    rc_level g (rc_root g v) = 0 := by
  rw [rc_level_zero_iff]
  exact rc_root_periodic g v

end RoadColoring
end
end MetaMathlibExt
