/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.LinearAlgebra.Dimension.Finite
import Def.Algebra.Lie.FreeLieMultihomogeneousComponent
import Def.Algebra.Lie.WittMultigradedValue
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Rotate
import Theorem.Combinatorics.Words.LyndonWord.Part14
import Lemma.Finset.Words.LyndonWord
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeAlgebra
import Def.Algebra.Lie.WittMultigradedDimension
open scoped BigOperators

/-!
# Witt's multigraded dimension formula

This file proves the multigraded dimension formula for a finitely generated free Lie algebra,
using the Lyndon-word basis and the enumeration of Lyndon words with prescribed content.
-/


namespace MetaMathlibExt

theorem wittLyndon_iff_suffix {α : Type*} [LinearOrder α] (w : List α) :
    IsLyndonWord w ↔ WittSuffixLyndon w := by
  constructor
  · rintro ⟨hwne, hrot⟩
    refine ⟨hwne, ?_⟩
    intro u v hune hvne hw
    subst w
    have hu0 : 0 < u.length := List.length_pos_of_ne_nil hune
    have hv0 : 0 < v.length := List.length_pos_of_ne_nil hvne
    have hlen : u.length < (u ++ v).length := by
      rw [List.length_append]
      exact Nat.lt_add_of_pos_right hv0
    have h₁ := hrot u.length hu0 hlen
    rw [List.rotate_append_length_eq] at h₁
    by_contra huv
    have hvw : v < u ++ v := lt_of_le_of_ne (le_of_not_gt huv) (by
      intro h
      have := congr_arg List.length h
      simp only [List.length_append] at this
      omega)
    by_cases hp : v <+: u ++ v
    · obtain ⟨t, ht⟩ := hp
      have htlen : t.length = u.length := by
        have := congr_arg List.length ht
        simp at this ⊢
        omega
      have htu : t < u := by
        rw [← ht, wittAppend_left_lt_iff] at h₁
        exact h₁
      have htuv : t ++ v < u ++ v := wittAppend_right_lt_of_length_eq htu htlen v
      have h₂ := hrot v.length hv0 (by simp; omega)
      rw [← ht, List.rotate_append_length_eq] at h₂
      rw [← ht] at htuv
      exact lt_asymm h₂ htuv
    · have hvrot : v ++ u < u ++ v := wittAppend_lt_of_lt_of_not_prefix hvw hp u
      exact lt_asymm h₁ hvrot
  · rintro ⟨hwne, hsuffix⟩
    refine ⟨hwne, ?_⟩
    intro k hk0 hk
    let u := w.take k
    let v := w.drop k
    have hune : u ≠ [] := by
      apply List.ne_nil_of_length_pos
      simp [u]
      omega
    have hvne : v ≠ [] := by
      apply List.ne_nil_of_length_pos
      simp [v]
      omega
    have hw : w = u ++ v := (List.take_append_drop k w).symm
    have hwv : w < v := hsuffix u v hune hvne hw
    rw [List.rotate_eq_drop_append_take hk.le]
    change w < v ++ u
    change List.Lex (· < ·) w (v ++ u)
    exact List.Lex.append_right (· < ·) u hwv

theorem wittSuffixLyndon_singleton {α : Type*} [LinearOrder α] (a : α) :
    WittSuffixLyndon [a] := by
  refine ⟨by simp, ?_⟩
  intro u v hu hv h
  have hu0 := List.length_pos_of_ne_nil hu
  have hv0 := List.length_pos_of_ne_nil hv
  have := congr_arg List.length h
  simp only [List.length_cons, List.length_nil, List.length_append] at this
  omega

theorem wittAppend_lt_right_of_lyndon_lt {α : Type*} [LinearOrder α]
    {u v : List α} (hu : u ≠ []) (hv : WittSuffixLyndon v) (huv : u < v) :
    u ++ v < v := by
  by_cases hp : u <+: v
  · obtain ⟨t, ht⟩ := hp
    have htne : t ≠ [] := by
      intro ht0
      subst t
      simp only [List.append_nil] at ht
      subst v
      exact lt_irrefl u huv
    have hvt : v < t := hv.2 u t hu htne ht.symm
    rw [← ht, wittAppend_left_lt_iff]
    rw [← ht] at hvt
    exact hvt
  · exact wittAppend_lt_of_lt_of_not_prefix huv hp v

theorem wittSuffixLyndon_append {α : Type*} [LinearOrder α]
    {u v : List α} (hu : WittSuffixLyndon u) (hv : WittSuffixLyndon v) (huv : u < v) :
    WittSuffixLyndon (u ++ v) := by
  have huv_v : u ++ v < v := wittAppend_lt_right_of_lyndon_lt hu.1 hv huv
  refine ⟨by simp [hu.1], ?_⟩
  intro a s hane hsne heq
  rcases List.append_eq_append_iff.mp heq with h | h
  · obtain ⟨x, ha, hvx⟩ := h
    by_cases hx : x = []
    · subst x
      simp only [List.nil_append] at hvx
      subst s
      exact huv_v
    · exact huv_v.trans (hv.2 x s hx hsne hvx)
  · obtain ⟨x, hua, hsx⟩ := h
    by_cases hx : x = []
    · subst x
      simp only [List.nil_append] at hsx
      subst s
      exact huv_v
    · have hux : u < x := hu.2 a x hane hx hua
      have hnpre : ¬u <+: x := by
        intro hp
        obtain ⟨z, hz⟩ := hp
        have hlen₁ := congr_arg List.length hua
        have hlen₂ := congr_arg List.length hz
        simp only [List.length_append] at hlen₁ hlen₂
        have ha0 := List.length_pos_of_ne_nil hane
        omega
      have hlt : u ++ v < x := wittAppend_lt_of_lt_of_not_prefix hux hnpre v
      have hlt' : u ++ v < x ++ v := by
        change List.Lex (· < ·) (u ++ v) (x ++ v)
        exact List.Lex.append_right (· < ·) v hlt
      simpa [hsx] using hlt'

theorem wittExists_lyndonSuffixIndex {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length) :
    ∃ k, 0 < k ∧ k < w.length ∧ WittSuffixLyndon (w.drop k) := by
  let k := w.length - 1
  have hk0 : 0 < k := by dsimp [k]; omega
  have hkw : k < w.length := by dsimp [k]; omega
  have hlen : (w.drop k).length = 1 := by simp [k]; omega
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
  exact ⟨k, hk0, hkw, ha ▸ wittSuffixLyndon_singleton a⟩

end MetaMathlibExt
