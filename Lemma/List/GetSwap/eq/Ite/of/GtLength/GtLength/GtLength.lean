import Lemma.Nat.Lt.ou.Eq.ou.Gt
import Lemma.List.GetSwap.eq.Ite.of.GtLength.GtLength.Lt
import Lemma.List.EqSwapS
import Lemma.List.EqSwap
import Lemma.List.LengthSwap.eq.Length
open List Nat


@[main]
private lemma main
  {a : List α}
  {i j t : ℕ}
-- given
  (h₀ : a.length > i)
  (h₁ : a.length > j)
  (h₂ : a.length > t) :
-- imply
  have : t < (a.swap i j).length := by
    rwa [LengthSwap.eq.Length]
  (a.swap i j)[t] =
    if t = i then
      a[j]
    else if t = j then
      a[i]
    else
      a[t] := by
-- proof
  intro h₃
  rcases (Lt.ou.Eq.ou.Gt i j) with h | h | h
  ·
    apply GetSwap.eq.Ite.of.GtLength.GtLength.Lt h h₁ h₂
  ·
    simp [h]
    simp [EqSwap]
    split_ifs with h
    ·
      simp_all
    ·
      rfl
  ·
    rw [EqSwapS] at h₃
    have := GetSwap.eq.Ite.of.GtLength.GtLength.Lt h h₀ h₂
    simp [EqSwapS] at this
    rw [this]
    split_ifs with h_j? h_i h_lt
    ·
      simp_all
    ·
      rfl
    ·
      rfl
    ·
      rfl


-- created on 2025-06-07
-- updated on 2025-06-28
