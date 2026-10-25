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
import Instance.Combinatorics.RoadColoring
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

theorem rc_translate_B_to_delta {V : Type*} {k : ℕ}
    (delta : V → Fin k → V)
    (sigma' : Quotient (rc_stableSetoid delta) → Equiv.Perm (Fin k))
    (u : List (Fin k)) (x y : V) (hst : rc_stable delta x y) :
    ∃ u' : List (Fin k),
      List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) x u =
        List.foldl delta x u' ∧
      List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) y u =
        List.foldl delta y u' := by
  induction u generalizing x y with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons c t ih =>
    have hclass : Quotient.mk (rc_stableSetoid delta) x = Quotient.mk _ y :=
      Quotient.sound hst
    have hsigP : sigma' (Quotient.mk _ y) = sigma' (Quotient.mk _ x) := by
      rw [hclass]
    have hst1 : rc_stable delta (delta x (sigma' (Quotient.mk _ x) c))
        (delta y (sigma' (Quotient.mk _ x) c)) :=
      rc_stable_foldl delta hst [sigma' (Quotient.mk _ x) c]
    obtain ⟨t', ht1, ht2⟩ := ih _ _ hst1
    refine ⟨sigma' (Quotient.mk _ x) c :: t', ?_, ?_⟩
    · change List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v)))
          (delta x (sigma' (Quotient.mk _ x) c)) t =
        List.foldl delta (delta x (sigma' (Quotient.mk _ x) c)) t'
      exact ht1
    · change List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v)))
          (delta y (sigma' (Quotient.mk _ y) c)) t =
        List.foldl delta (delta y (sigma' (Quotient.mk _ x) c)) t'
      rw [hsigP]
      exact ht2

theorem rc_translate_delta_to_B {V : Type*} {k : ℕ}
    (delta : V → Fin k → V)
    (sigma' : Quotient (rc_stableSetoid delta) → Equiv.Perm (Fin k))
    (u' : List (Fin k)) (x y : V) (hst : rc_stable delta x y) :
    ∃ u : List (Fin k),
      List.foldl delta x u' =
        List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) x u ∧
      List.foldl delta y u' =
        List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) y u := by
  induction u' generalizing x y with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons d t' ih =>
    have hclass : Quotient.mk (rc_stableSetoid delta) x = Quotient.mk _ y :=
      Quotient.sound hst
    have hsigP : sigma' (Quotient.mk _ y) = sigma' (Quotient.mk _ x) := by
      rw [hclass]
    have hst1 : rc_stable delta (delta x d) (delta y d) :=
      rc_stable_foldl delta hst [d]
    obtain ⟨u_tail, ht1, ht2⟩ := ih _ _ hst1
    have hBxc : (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) x
        ((sigma' (Quotient.mk _ x)).symm d) = delta x d := by
      change delta x (sigma' (Quotient.mk _ x) ((sigma' (Quotient.mk _ x)).symm d)) =
        delta x d
      rw [Equiv.apply_symm_apply]
    have hByc : (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) y
        ((sigma' (Quotient.mk _ x)).symm d) = delta y d := by
      change delta y (sigma' (Quotient.mk _ y) ((sigma' (Quotient.mk _ x)).symm d)) =
        delta y d
      rw [hsigP, Equiv.apply_symm_apply]
    refine ⟨(sigma' (Quotient.mk _ x)).symm d :: u_tail, ?_, ?_⟩
    · change List.foldl delta (delta x d) t' =
        List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v)))
          ((rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) x
            ((sigma' (Quotient.mk _ x)).symm d)) u_tail
      rw [hBxc]
      exact ht1
    · change List.foldl delta (delta y d) t' =
        List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v)))
          ((rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) y
            ((sigma' (Quotient.mk _ x)).symm d)) u_tail
      rw [hByc]
      exact ht2

theorem rc_stable_lift {V : Type*} {k : ℕ}
    (delta : V → Fin k → V)
    (sigma' : Quotient (rc_stableSetoid delta) → Equiv.Perm (Fin k))
    {x y : V} (hst : rc_stable delta x y) :
    rc_stable (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) x y := by
  intro u
  obtain ⟨u', hu1, hu2⟩ := rc_translate_B_to_delta delta sigma' u x y hst
  obtain ⟨v', hv⟩ := rc_stable_merge delta (rc_stable_foldl delta hst u')
  obtain ⟨v, hv1, hv2⟩ := rc_translate_delta_to_B delta sigma' v' _ _
    (rc_stable_foldl delta hst u')
  refine ⟨v, ?_⟩
  rw [List.foldl_append, List.foldl_append, hu1, hu2, ← hv1, ← hv2]
  exact hv

end RoadColoring
end
end MetaMathlibExt
