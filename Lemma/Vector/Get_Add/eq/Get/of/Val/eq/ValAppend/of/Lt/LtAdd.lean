import Lemma.Bool.EqUFnS.of.Eq
import Lemma.Vector.ValAppend.eq.AppendValS
import Lemma.List.LengthAppend.eq.AddLengthS
import Lemma.List.EqGetS.of.Eq.GtLength
open List Vector Bool


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
