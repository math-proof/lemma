import Lemma.List.LengthInsertIdx.eq.Add1Length.of.Le_Length
import Lemma.Nat.Le_Sub_1.of.Lt
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.Lt_Length
import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.Nat.Ge_1.of.Gt
open List Nat


@[main]
private lemma main
  {dim : ℕ}
  {s : List α}
-- given
  (h : dim < s.length)
  (a : α) :
-- imply
  ((s.eraseIdx dim).insertIdx dim a).length = s.length := by
-- proof
  rw [LengthInsertIdx.eq.Add1Length.of.Le_Length] <;>
    rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length h]
  ·
    apply (EqAdd_Sub.of.Ge ∘ Ge_1.of.Gt) h
  ·
    apply Le_Sub_1.of.Lt h


-- created on 2025-10-04
