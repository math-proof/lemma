import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.NumberTheory.GesselWord


namespace MetaMathlibExt

/--
[eq_nil_or_eq_singleton_or_eq_pair_of_append_eq_pair](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/GesselWord.lean)
-/
@[path]
private lemma eq_nil_or_eq_singleton_or_eq_pair_of_append_eq_pair
  {α : Type*} (a b : α) (w' suffix : List α) (h : w' ++ suffix = [a, b]) :
  w' = [] ∨ w' = [a] ∨ w' = [a, b] := by
  cases w' with
  | nil => exact Or.inl rfl
  | cons head tail =>
    simp only [List.cons_append] at h
    rw [List.cons.injEq] at h
    obtain ⟨rfl, htail⟩ := h
    cases tail with
    | nil => exact Or.inr (Or.inl rfl)
    | cons second rest =>
      simp only [List.cons_append] at htail
      rw [List.cons.injEq] at htail
      obtain ⟨rfl, hrest⟩ := htail
      cases rest with
      | nil => exact Or.inr (Or.inr rfl)
      | cons third rest =>
        have := congrArg List.length hrest
        simp at this

end MetaMathlibExt


-- created on 2026-10-23
