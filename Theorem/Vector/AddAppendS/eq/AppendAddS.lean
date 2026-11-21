module
public import Initialize.Tactic.Attr.Basic
public import Theorem.Data.Vector.Basic
public import Instance.Data.Vector.Basic.Arithmetic


@[path]
theorem main
  [Add α]
-- given
  (a c : List.Vector α n)
  (b d : List.Vector α m) :
-- imply
  a ++ b + (c ++ d) = a + c ++ (b + d) := by
-- proof
  apply Subtype.ext
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  obtain ⟨c, hc⟩ := c
  obtain ⟨d, hd⟩ := d
  apply List.zipWith_append
  rw [ha, hc]


-- created on 2026-08-23
