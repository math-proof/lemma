import Lemma.List.Swap
import Lemma.List.LengthSwap.eq.Length
import Lemma.List.GetElemSwap.eq.SomeGet
open List


@[main]
private lemma main
  {s : List α}
  {i j : ℕ}
-- given
  (h₀ : s.length > j)
  (h₁ : s.length > i) :
-- imply
  have : i < (s.swap i j).length := by rwa [LengthSwap.eq.Length]
  (s.swap i j)[i] = s[j] := by
-- proof
  let i : Fin s.length := ⟨i, h₁⟩
  let j : Fin s.length := ⟨j, h₀⟩
  have h_eq := GetElemSwap.eq.SomeGet s i j
  aesop


@[main]
private lemma left
  {s : List α}
  {i j : ℕ}
-- given
  (h₀ : s.length > i)
  (h₁ : s.length > j) :
-- imply
  have : j < (s.swap i j).length := by rwa [LengthSwap.eq.Length]
  (s.swap i j)[j] = s[i] := by
-- proof
  let i : Fin s.length := ⟨i, h₀⟩
  let j : Fin s.length := ⟨j, h₁⟩
  have h_eq := GetElemSwap.eq.SomeGet s j i
  rw [Swap] at h_eq
  aesop


-- created on 2025-05-17
