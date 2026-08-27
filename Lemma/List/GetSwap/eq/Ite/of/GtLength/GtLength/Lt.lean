import Batteries.Data.List.Lemmas
import Lemma.Nat.Lt.of.Lt.Lt
open Nat


@[main]
private lemma main
  {s : List α}
  {i j t : ℕ}
-- given
  (h₀ : i < j)
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
  have h_i := Lt.of.Lt.Lt h₀ h₁
  rw [List.getElem_swap h₃]
  simp [h₁, h_i]
  split_ifs <;> rfl


-- created on 2025-06-07
-- updated on 2026-08-24
