import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.Expander


namespace SimpleGraph.ExpanderTest

/--
[card_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Expander.lean)
-/
@[path]
private lemma card_threshold :
  (Nat.card (Fin 4) : ℝ) / (2 * (1 : ℝ)) = 2 := by
  have hc : Nat.card (Fin 4) = 4 := by simp
  rw [hc]
  norm_num

end SimpleGraph.ExpanderTest

namespace SimpleGraph.ExpanderTest

/--
[one_le_external_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Expander.lean)
-/
@[path]
private lemma one_le_external_singleton (a : Fin 4) :
  (1 : ℝ) ≤
    (((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {a}).ncard :
      ℝ) := by
  fin_cases a
  · have hsub : ({1} : Set (Fin 4)) ⊆
    (SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {0} := by
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp only [SimpleGraph.mem_externalNeighborSet]
    exact ⟨by decide, 0, by decide, by decide⟩
    have hle : ({1} : Set (Fin 4)).ncard ≤
      ((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {0}).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at hle
    have hleR : ((1 : ℕ) : ℝ) ≤
      ((((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {0}).ncard :
        ℝ)) :=
      Nat.cast_le.mpr hle
    simpa using hleR
  · have hsub : ({0} : Set (Fin 4)) ⊆
    (SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {1} := by
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp only [SimpleGraph.mem_externalNeighborSet]
    exact ⟨by decide, 1, by decide, by decide⟩
    have hle : ({0} : Set (Fin 4)).ncard ≤
      ((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {1}).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at hle
    have hleR : ((1 : ℕ) : ℝ) ≤
      ((((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {1}).ncard :
        ℝ)) :=
      Nat.cast_le.mpr hle
    simpa using hleR
  · have hsub : ({0} : Set (Fin 4)) ⊆
    (SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {2} := by
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp only [SimpleGraph.mem_externalNeighborSet]
    exact ⟨by decide, 2, by decide, by decide⟩
    have hle : ({0} : Set (Fin 4)).ncard ≤
      ((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {2}).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at hle
    have hleR : ((1 : ℕ) : ℝ) ≤
      ((((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {2}).ncard :
        ℝ)) :=
      Nat.cast_le.mpr hle
    simpa using hleR
  · have hsub : ({0} : Set (Fin 4)) ⊆
    (SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {3} := by
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp only [SimpleGraph.mem_externalNeighborSet]
    exact ⟨by decide, 3, by decide, by decide⟩
    have hle : ({0} : Set (Fin 4)).ncard ≤
      ((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {3}).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at hle
    have hleR : ((1 : ℕ) : ℝ) ≤
      ((((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {3}).ncard :
        ℝ)) :=
      Nat.cast_le.mpr hle
    simpa using hleR

end SimpleGraph.ExpanderTest

namespace SimpleGraph.ExpanderTest

/--
[four_expander](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Expander.lean)
-/
@[path]
private lemma four_expander :
  (SimpleGraph.completeGraph (Fin 4)).IsCExpander 1 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro A hA
    rw [card_threshold] at hA
    have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    have hAlt : (A.ncard : ℝ) < ((2 : ℕ) : ℝ) := by rw [hcast]; exact hA
    have hAn : A.ncard < 2 := Nat.cast_lt.mp hAlt
    have h01 : A.ncard = 0 ∨ A.ncard = 1 := by omega
    obtain h0 | h1 := h01
    · simp only [h0, Nat.cast_zero, one_mul]
      exact Nat.cast_nonneg _
    · obtain ⟨a, rfl⟩ := Set.ncard_eq_one.mp h1
      have e1 : ((({a} : Set (Fin 4)).ncard : ℝ)) = 1 := by
        simp [Set.ncard_singleton]
      rw [e1, one_mul]
      exact one_le_external_singleton a
  · intro A B hdis hA hB
    rw [card_threshold] at hA hB
    have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    have hAcast : ((2 : ℕ) : ℝ) ≤ (A.ncard : ℝ) := by rw [hcast]; exact hA
    have hBcast : ((2 : ℕ) : ℝ) ≤ (B.ncard : ℝ) := by rw [hcast]; exact hB
    have hA2 : 2 ≤ A.ncard := Nat.cast_le.mp hAcast
    have hB2 : 2 ≤ B.ncard := Nat.cast_le.mp hBcast
    have hAne : A.Nonempty := by
      by_contra hcon
      have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hcon
      rw [he, Set.ncard_empty] at hA2
      exact (by decide : ¬ (2 ≤ (0 : ℕ))) hA2
    have hBne : B.Nonempty := by
      by_contra hcon
      have he : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hcon
      rw [he, Set.ncard_empty] at hB2
      exact (by decide : ¬ (2 ≤ (0 : ℕ))) hB2
    obtain ⟨a, ha⟩ := hAne
    obtain ⟨b, hb⟩ := hBne
    have hne : a ≠ b := by
      intro heq
      subst heq
      exact (Set.disjoint_left.mp hdis ha) hb
    exact ⟨a, ha, b, hb, hne⟩

end SimpleGraph.ExpanderTest


-- created on 2026-10-23
