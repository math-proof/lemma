import Lemma.List.GetElem.eq.SomeGet.of.GtLength
import Lemma.List.LengthEnumerate.eq.Length
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  s.enumerate[i]? = some ⟨⟨i, h⟩, s[i]⟩ := by
-- proof
  have := LengthEnumerate.eq.Length s
  rw [← this] at h
  have := GetElem.eq.SomeGet.of.GtLength h
  rw [this]
  congr
  simp [List.enumerate]


-- created on 2025-06-02
