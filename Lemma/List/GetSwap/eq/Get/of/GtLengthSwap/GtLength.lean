import Lemma.List.EqSwapS
import Lemma.List.LengthSwap.eq.Length
import Lemma.List.GetElemSwap.eq.SomeGet
open List


@[main]
private lemma main
  {a : List α}
  {i j : ℕ}
-- given
  (h₀ : a.length > j)
  (h₁ : a.length > i) :
-- imply
  have : i < (a.swap i j).length := by rwa [LengthSwap.eq.Length]
  (a.swap i j)[i] = a[j] := by
-- proof
  let i : Fin a.length := ⟨i, h₁⟩
  let j : Fin a.length := ⟨j, h₀⟩
  have h_eq := GetElemSwap.eq.SomeGet a i j
  aesop


@[main]
private lemma left
  {a : List α}
  {i j : ℕ}
-- given
  (h₀ : a.length > i)
  (h₁ : a.length > j) :
-- imply
  have : j < (a.swap i j).length := by rwa [LengthSwap.eq.Length]
  (a.swap i j)[j] = a[i] := by
-- proof
  let i : Fin a.length := ⟨i, h₀⟩
  let j : Fin a.length := ⟨j, h₁⟩
  have h_eq := GetElemSwap.eq.SomeGet a j i
  rw [EqSwapS] at h_eq
  aesop


-- created on 2025-05-17
