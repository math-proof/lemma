module

public import Theorem.List.GetElem.eq.SomeGet.of.GtLength
public import Theorem.List.LengthEnumerate.eq.Length

public section

open List


public theorem List.GetElemEnumerate.eq.Some.of.GtLength
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
