module

public import Batteries.Data.List.Lemmas
public import Theorem.Nat.Lt.of.Lt.Lt

public section

open Nat


public theorem List.GetSwap.eq.Ite.of.GtLength.GtLength.Lt
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
