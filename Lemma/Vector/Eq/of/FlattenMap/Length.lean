import Mathlib.Data.Vector.MapLemmas
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b : List (List.Vector α n)}
-- given
  (h₀ : a.length = b.length)
  (h₁ : (a.map List.Vector.toList).flatten = (b.map List.Vector.toList).flatten) :
-- imply
  a = b := by
-- proof
  induction a generalizing b with
  | nil =>
    cases b <;> simp_all
  | cons a₀ a ih =>
    cases b with
    | nil => simp at h₀
    | cons b₀ b =>
      simp only [List.length_cons, Nat.succ.injEq] at h₀
      simp only [List.map_cons, List.flatten_cons] at h₁
      obtain ⟨h_head, h_tail⟩ := List.append_inj h₁ (by simp)
      congr
      · apply Subtype.ext h_head
      · apply ih h₀ h_tail


-- created on 2025-05-11
-- updated on 2026-11-20
