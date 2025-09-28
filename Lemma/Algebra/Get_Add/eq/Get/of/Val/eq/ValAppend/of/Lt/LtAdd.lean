import Lemma.Logic.EqUFnS.of.Eq
import Lemma.Algebra.ValAppend.eq.AppendValS
import Lemma.Algebra.LengthAppend.eq.AddLengthS
import Lemma.Algebra.EqGetS.of.Eq.Lt_Length
open Algebra Logic


@[main]
private lemma main
  {a : List.Vector α N}
  {b : List.Vector α m}
  {c : List.Vector α n}
-- given
  (h₀ : m + i < N)
  (h₁ : i < n)
  (h₂ : a.val = (b ++ c).val) :
-- imply
  a[m + i] = c[i] := by
-- proof
  rw [ValAppend.eq.AppendValS] at h₂
  simp only [GetElem.getElem]
  simp_all [List.Vector.get]


-- created on 2025-05-31
