import Batteries.Data.List.Lemmas
import sympy.Basic


@[main]
private lemma main
  {s : List α}
  {i j t : ℕ}
-- given
  (h₀ : s.length > i)
  (h₁ : s.length > j)
  (h₂ : s.length > t) :
-- imply
  have : t < (s.swap i j).length := by simp_all [List.length_swap]
  (s.swap i j)[t] =
    if t = i then
      s[j]
    else if t = j then
      s[i]
    else
      s[t] := by
-- proof
  intro h₃
  rw [List.getElem_swap h₃]
  simp [h₀, h₁]
  grind


-- created on 2025-06-07
-- updated on 2026-08-24
