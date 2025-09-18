import Lemma.Algebra.EqSwapS
import Lemma.Algebra.LengthSwap.eq.Length
import Lemma.Algebra.GetElem!Swap.eq.SomeGet
open Algebra


@[main]
private lemma main
  {a : List α}
  {i j : ℕ}
-- given
  (h₀ : j < a.length)
  (h₁ : i < a.length) :
-- imply
  have : i < (a.swap i j).length := by rwa [LengthSwap.eq.Length]
  (a.swap i j)[i] = a[j] := by
-- proof
  let i : Fin a.length := ⟨i, h₁⟩
  let j : Fin a.length := ⟨j, h₀⟩
  have h_eq := GetElem!Swap.eq.SomeGet a i j
  aesop


@[main]
private lemma left
  {a : List α}
  {i j : ℕ}
-- given
  (h₀ : i < a.length)
  (h₁ : j < a.length) :
-- imply
  have : j < (a.swap i j).length := by rwa [LengthSwap.eq.Length]
  (a.swap i j)[j] = a[i] := by
-- proof
  let i : Fin a.length := ⟨i, h₀⟩
  let j : Fin a.length := ⟨j, h₁⟩
  have h_eq := GetElem!Swap.eq.SomeGet a j i
  rw [EqSwapS] at h_eq
  aesop


-- created on 2025-05-17
