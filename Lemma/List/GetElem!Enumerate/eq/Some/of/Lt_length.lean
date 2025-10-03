import Lemma.List.GetElem!.eq.SomeGet.of.Lt
import Lemma.List.LengthEnumerate.eq.Length
open List


@[main]
private lemma main
  {a : List α}
-- given
  (h : i < a.length) :
-- imply
  a.enumerate[i]? = some ⟨⟨i, h⟩, a[i]⟩ := by
-- proof
  have := LengthEnumerate.eq.Length a
  rw [← this] at h
  have := GetElem!.eq.SomeGet.of.Lt h
  rw [this]
  congr
  simp [List.enumerate]


-- created on 2025-06-02
