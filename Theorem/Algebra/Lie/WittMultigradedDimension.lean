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
open scoped BigOperators

/-!
# Witt's multigraded dimension formula

This file proves the multigraded dimension formula for a finitely generated free Lie algebra,
using the Lyndon-word basis and the enumeration of Lyndon words with prescribed content.
-/


namespace MetaMathlibExt

theorem wittAppend_left_lt_iff {α : Type*} [LinearOrder α]
    (s a b : List α) : s ++ a < s ++ b ↔ a < b := by
  induction s with
  | nil => simp
  | cons x s ih =>
      change List.Lex (· < ·) (x :: (s ++ a)) (x :: (s ++ b)) ↔ a < b
      rw [List.lex_cons_iff]
      exact ih

theorem wittAppend_right_lt_of_length_eq {α : Type*} [LinearOrder α]
    {a b : List α} (h : a < b) (hlen : a.length = b.length) (c : List α) :
    a ++ c < b ++ c := by
  change List.Lex (· < ·) a b at h
  change List.Lex (· < ·) (a ++ c) (b ++ c)
  induction h with
  | nil => simp at hlen
  | rel hab => exact .rel hab
  | cons h ih => exact .cons (ih (Nat.succ.inj hlen))

theorem wittAppend_lt_of_lt_of_not_prefix {α : Type*} [LinearOrder α]
    {a b : List α} (h : a < b) (hp : ¬a <+: b) (c : List α) : a ++ c < b := by
  change List.Lex (· < ·) a b at h
  change List.Lex (· < ·) (a ++ c) b
  induction h with
  | @nil x l => exact (hp ⟨x :: l, rfl⟩).elim
  | rel hab => exact .rel hab
  | @cons x l₁ l₂ h ih =>
      apply List.Lex.cons
      apply ih
      intro hpre
      obtain ⟨t, ht⟩ := hpre
      exact hp ⟨t, by simp [ht]⟩

theorem wittLe_append_self {α : Type*} [LinearOrder α] (a c : List α) :
    a ≤ a ++ c := by
  cases c with
  | nil => simp
  | cons x c =>
      apply le_of_lt
      change List.Lex (· < ·) a (a ++ x :: c)
      induction a with
      | nil => exact .nil
      | cons y a ih => exact .cons ih

theorem wittAppend_lt_right_imp_left_lt {α : Type*} [LinearOrder α]
    {a b : List α} (h : a ++ b < b) : a < b := by
  by_contra hab
  have hba : b ≤ a := le_of_not_gt hab
  rcases hba.eq_or_lt with hba | hba
  · subst b
    exact (not_lt_of_ge (wittLe_append_self a a)) h
  · by_cases hp : b <+: a
    · obtain ⟨t, ht⟩ := hp
      have hbpre : b <+: a ++ b := by
        exact ⟨t ++ b, by simpa [List.append_assoc] using congr_arg (fun z => z ++ b) ht⟩
      obtain ⟨z, hz⟩ := hbpre
      have hble : b ≤ a ++ b := by rw [← hz]; exact wittLe_append_self b z
      exact (not_lt_of_ge hble) h
    · have hlt : b ++ b < a := wittAppend_lt_of_lt_of_not_prefix hba hp b
      have hcycle : b ++ b < b :=
        (hlt.trans_le (wittLe_append_self a b)).trans h
      exact (not_lt_of_ge (wittLe_append_self b b)) hcycle

end MetaMathlibExt
