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
import Def.Combinatorics.RoadColoring.Part6
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

theorem rc_update_level_eq {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (x y : V) (v : V) (havoid : ∀ i : ℕ, R^[i] v ≠ x) :
    rc_level (Function.update R x y) v = rc_level R v := by
  have agree : ∀ j : ℕ, (Function.update R x y)^[j] v = R^[j] v :=
    fun j => rc_update_iterate_agree R x y v havoid j
  have hz : ∀ i : ℕ, R^[i] (R^[rc_level R v] v) ≠ x := by
    intro i
    have e : R^[i] (R^[rc_level R v] v) = R^[rc_level R v + i] v := by
      rw [Nat.add_comm (rc_level R v) i, Function.iterate_add_apply]
    rw [e]
    exact havoid _
  have hagree2 : ∀ j : ℕ, (Function.update R x y)^[j]
      (R^[rc_level (Function.update R x y) v] v) = R^[j]
      (R^[rc_level (Function.update R x y) v] v) := by
    intro j
    have h1 := agree (rc_level (Function.update R x y) v + j)
    rw [Nat.add_comm (rc_level (Function.update R x y) v) j,
      Function.iterate_add_apply, Function.iterate_add_apply,
      agree (rc_level (Function.update R x y) v)] at h1
    exact h1
  have eL : (Function.update R x y)^[rc_level R v] v = R^[rc_level R v] v :=
    agree _
  have h1mem : R^[rc_level R v] v ∈ Function.periodicPts (Function.update R x y) :=
    rc_update_periodic R x y _ hz (rc_level_spec R v)
  rw [← eL] at h1mem
  have eL1 : (Function.update R x y)^[rc_level (Function.update R x y) v] v =
      R^[rc_level (Function.update R x y) v] v := agree _
  have hper1 : R^[rc_level (Function.update R x y) v] v ∈
      Function.periodicPts (Function.update R x y) := by
    rw [← eL1]
    exact rc_level_spec _ v
  exact Nat.le_antisymm
    (rc_level_le_of_mem _ _ h1mem)
    (rc_level_le_of_mem _ _ (rc_update_periodic_of R x y _ hagree2 hper1))

theorem rc_level_along_orbit {V : Type*} [Finite V] (g : V → V) (v : V) :
    ∀ (i : ℕ), i ≤ rc_level g v →
    rc_level g (g^[i] v) = rc_level g v - i := by
  intro i
  induction i with
  | zero => intro _; simp only [Function.iterate_zero_apply, Nat.sub_zero]
  | succ i ih =>
    intro hi
    have hiL : i ≤ rc_level g v := by omega
    have eih := ih hiL
    have hnon : g^[i] v ∉ Function.periodicPts g := by
      intro hmem
      have h0 : rc_level g (g^[i] v) = 0 := (rc_level_zero_iff g _).mpr hmem
      omega
    have estep := rc_level_step g (g^[i] v) hnon
    have eiter : g^[i + 1] v = g (g^[i] v) := by
      rw [show i + 1 = (i).succ from rfl]
      exact Function.iterate_succ_apply' g i v
    rw [eiter, estep, eih]
    omega

theorem rc_root_along_orbit {V : Type*} [Finite V] (g : V → V) (v : V)
    {i : ℕ} (hi : i ≤ rc_level g v) :
    rc_root g (g^[i] v) = rc_root g v := by
  unfold rc_root
  rw [rc_level_along_orbit g v i hi, ← Function.iterate_add_apply]
  have hii : rc_level g v - i + i = rc_level g v := by omega
  rw [hii]

end RoadColoring
end
end MetaMathlibExt
