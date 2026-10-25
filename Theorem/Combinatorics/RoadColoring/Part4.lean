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
import Def.Combinatorics.RoadColoring.Part4
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

theorem rc_iterate_ge_level_periodic {V : Type*} [Finite V]
    (g : V → V) (v : V) {j : ℕ} (hj : rc_level g v ≤ j) :
    g^[j] v ∈ Function.periodicPts g := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_comm (rc_level g v) d, Function.iterate_add_apply]
  exact rc_periodic_iterate g (rc_level_spec g v) d

theorem rc_iterate_height_periodic {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V) (v : V) : g^[rc_height g] v ∈ Function.periodicPts g :=
  rc_iterate_ge_level_periodic g v (rc_level_le_height g v)

theorem rc_pred_notMem_of_top {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V) {p : V} (hp : rc_level g p = rc_height g)
    (hH : 1 ≤ rc_height g) : g^[rc_height g - 1] p ∉ Function.periodicPts g := by
  intro hmem
  have hle := rc_level_le_of_mem g p hmem
  omega

theorem rc_level_eq_height_of_pred_notMem {V : Type*} [Fintype V]
    [DecidableEq V] (g : V → V) (L : ℕ) (hL : rc_height g = L)
    (v : V) (hv : g^[L - 1] v ∉ Function.periodicPts g) (hL1 : 1 ≤ L) :
    rc_level g v = L := by
  have hle : rc_level g v ≤ L := by rw [← hL]; exact rc_level_le_height g v
  by_contra hne
  have hlt : rc_level g v < L := by omega
  have hmem : g^[L - 1] v ∈ Function.periodicPts g := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show rc_level g v ≤ L - 1 by omega)
    have hspec := rc_level_spec g v
    have e : L - 1 = rc_level g v + d := hd
    rw [e, Nat.add_comm (rc_level g v) d, Function.iterate_add_apply]
    exact rc_periodic_iterate g hspec d
  exact hv hmem

theorem rc_good_bridge {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (g : V → V) (hgood : rc_good g) :
    ∃ (L : ℕ) (r p : V), 1 ≤ L ∧ L = rc_height g ∧ rc_level g p = rc_height g ∧
      r = rc_root g p ∧ (∀ v, g^[L] v ∈ Function.periodicPts g) ∧
      g^[L - 1] p ∉ Function.periodicPts g ∧
      (∀ v, g^[L - 1] v ∉ Function.periodicPts g → g^[L] v = r) := by
  classical
  obtain ⟨hHpos, huniq⟩ := hgood
  obtain ⟨p, hp⟩ := rc_height_attained g
  have hH1 : 1 ≤ rc_height g := hHpos
  refine ⟨rc_height g, rc_root g p, p, hH1, rfl, hp, rfl, ?_, ?_, ?_⟩
  · intro v
    exact rc_iterate_height_periodic g v
  · exact rc_pred_notMem_of_top g hp hH1
  · intro v hv
    have hLv : rc_level g v = rc_height g :=
      rc_level_eq_height_of_pred_notMem g (rc_height g) rfl v hv hH1
    have e1 : g^[rc_height g] v = rc_root g v := by
      unfold rc_root
      rw [hLv]
    have e2 : rc_root g v = rc_root g p := huniq v p hLv hp
    rw [e1, e2]

end RoadColoring
end
end MetaMathlibExt
