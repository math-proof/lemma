import Lemma.List.Rotate.eq.AppendDrop__Take.of.Le_Length
import Lemma.List.LengthRotate.eq.Length
import Lemma.List.DropAppend.eq.AppendDropS
import Lemma.Nat.EqAdd_Sub.of.Ge
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h : i ≤ s.length) :
-- imply
  (s.rotate i).rotate (s.length - i) = s := by
-- proof
  repeat rw [Rotate.eq.AppendDrop__Take.of.Le_Length]
  · 
    simp [DropAppend.eq.AppendDropS _ _ (s.length - i)]
    rw [EqAdd_Sub.of.Ge h]
  · 
    exact h
  · 
    simp [LengthRotate.eq.Length s]


-- created on 2025-10-14
