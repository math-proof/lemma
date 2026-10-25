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
import Def.Combinatorics.RoadColoring
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

theorem rc_stable_refl {V : Type*} {k : ℕ} (delta : V → Fin k → V) (p : V) :
    rc_stable delta p p := fun u => ⟨[], by simp⟩

theorem rc_stable_symm {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    {p q : V} (h : rc_stable delta p q) : rc_stable delta q p :=
  fun u => by obtain ⟨v, hv⟩ := h u; exact ⟨v, hv.symm⟩

theorem rc_stable_trans {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    {p q s : V} (hpq : rc_stable delta p q) (hqs : rc_stable delta q s) :
    rc_stable delta p s := by
  intro u
  obtain ⟨v1, hv1⟩ := hpq u
  obtain ⟨v2, hv2⟩ := hqs (u ++ v1)
  refine ⟨v1 ++ v2, ?_⟩
  have assoc : (u ++ v1) ++ v2 = u ++ (v1 ++ v2) := List.append_assoc u v1 v2
  have ep : List.foldl delta p (u ++ (v1 ++ v2)) =
      List.foldl delta (List.foldl delta p (u ++ v1)) v2 := by
    rw [← assoc, List.foldl_append]
  have es : List.foldl delta s (u ++ (v1 ++ v2)) =
      List.foldl delta (List.foldl delta s (u ++ v1)) v2 := by
    rw [← assoc, List.foldl_append]
  have qe : List.foldl delta q ((u ++ v1) ++ v2) =
      List.foldl delta (List.foldl delta q (u ++ v1)) v2 :=
    List.foldl_append
  have se : List.foldl delta s ((u ++ v1) ++ v2) =
      List.foldl delta (List.foldl delta s (u ++ v1)) v2 :=
    List.foldl_append
  have hv2' : List.foldl delta (List.foldl delta q (u ++ v1)) v2 =
      List.foldl delta (List.foldl delta s (u ++ v1)) v2 := by
    rw [← qe, ← se]
    exact hv2
  calc List.foldl delta p (u ++ (v1 ++ v2))
      = List.foldl delta (List.foldl delta p (u ++ v1)) v2 := ep
    _ = List.foldl delta (List.foldl delta q (u ++ v1)) v2 := by rw [hv1]
    _ = List.foldl delta (List.foldl delta s (u ++ v1)) v2 := hv2'
    _ = List.foldl delta s (u ++ (v1 ++ v2)) := es.symm

theorem rc_stable_foldl {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    {p q : V} (h : rc_stable delta p q) (w : List (Fin k)) :
    rc_stable delta (List.foldl delta p w) (List.foldl delta q w) := by
  intro u
  obtain ⟨v, hv⟩ := h (w ++ u)
  refine ⟨v, ?_⟩
  have assoc : (w ++ u) ++ v = w ++ (u ++ v) := List.append_assoc w u v
  have e1 : List.foldl delta p ((w ++ u) ++ v) =
      List.foldl delta (List.foldl delta p w) (u ++ v) := by
    rw [assoc, List.foldl_append, List.foldl_append]
  have e2 : List.foldl delta q ((w ++ u) ++ v) =
      List.foldl delta (List.foldl delta q w) (u ++ v) := by
    rw [assoc, List.foldl_append, List.foldl_append]
  rw [e1] at hv
  rw [e2] at hv
  exact hv

theorem rc_exists_merge_of_pairwise_stable {V : Type*} [Nonempty V]
    {k : ℕ} (delta : V → Fin k → V) :
    ∀ S : Finset V, (∀ p ∈ S, ∀ q ∈ S, rc_stable delta p q) →
    ∃ w : List (Fin k), ∃ r : V, ∀ v ∈ S, List.foldl delta v w = r := by
  classical
  obtain ⟨r₀⟩ := (‹Nonempty V› : Nonempty V)
  have key : ∀ m : ℕ, ∀ T : Finset V, T.card ≤ m →
      (∀ p ∈ T, ∀ q ∈ T, rc_stable delta p q) →
      ∃ w : List (Fin k), ∃ r : V, ∀ v ∈ T, List.foldl delta v w = r := by
    intro m
    induction m with
    | zero =>
      intro T hcard h
      have hempty : T = ∅ := Finset.card_eq_zero.mp (by omega)
      exact ⟨[], r₀,
        fun v hv => by rw [hempty] at hv; exact absurd hv (Finset.notMem_empty v)⟩
    | succ m ih =>
      intro T hcard h
      by_cases hle : T.card ≤ 1
      · by_cases hT : T.Nonempty
        · obtain ⟨p, hp⟩ := hT
          refine ⟨[], p, fun v hv => ?_⟩
          have hvp : v = p := Finset.card_le_one_iff.mp hle hv hp
          rw [hvp]
          rfl
        · have hT' : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
          exact ⟨[], r₀,
            fun v hv => by rw [hT'] at hv; exact absurd hv (Finset.notMem_empty v)⟩
      · obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
        have hcardE : 0 < (T.erase p).card := by
          rw [Finset.card_erase_of_mem hp]
          omega
        obtain ⟨q, hq⟩ := Finset.card_pos.mp hcardE
        have hqT : q ∈ T := Finset.mem_of_mem_erase hq
        have hne : q ≠ p := Finset.ne_of_mem_erase hq
        obtain ⟨t, ht⟩ := rc_stable_merge delta (h p hp q hqT)
        have hlt : (T.image (fun x => List.foldl delta x t)).card < T.card := by
          by_contra hcon
          have hle2 := Finset.card_image_le (s := T)
            (f := fun x => List.foldl delta x t)
          have heq : (T.image (fun x => List.foldl delta x t)).card = T.card := by
            omega
          have hinj := Finset.card_image_iff.mp heq
          exact hne (hinj (Finset.mem_coe.mpr hp) (Finset.mem_coe.mpr hqT) ht).symm
        have hstab : ∀ y₁ ∈ T.image (fun x => List.foldl delta x t),
            ∀ y₂ ∈ T.image (fun x => List.foldl delta x t),
            rc_stable delta y₁ y₂ := by
          intro y₁ hy₁ y₂ hy₂
          obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp hy₁
          obtain ⟨x₂, hx₂, rfl⟩ := Finset.mem_image.mp hy₂
          exact rc_stable_foldl delta (h x₁ hx₁ x₂ hx₂) t
        obtain ⟨w', r, hr⟩ := ih _ (by omega) hstab
        exact ⟨t ++ w', r, fun v hv => by
          rw [List.foldl_append]
          exact hr _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)⟩
  intro S hS
  exact key S.card S le_rfl hS

end RoadColoring
end
end MetaMathlibExt
