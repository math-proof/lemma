import Def.Data.Vector.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Add α] [Zero α]
  {s : List.Vector α n}
-- given
  (h : n > 0) :
-- imply
  s.sum = s[0] + (s.drop 1).sum := by
-- proof
  obtain ⟨_ | ⟨head, tail⟩, hs⟩ := s
  ·
    simp at hs
    apply (Nat.ne_of_gt h).elim
    omega
  · rfl


-- created on 2026-07-11
-- updated on 2026-11-20
