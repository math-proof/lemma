import Lemma.Nat.CeilSub.eq.Sub_Floor
import Lemma.Nat.Ne_0.of.Gt
import Lemma.Rat.FloorDiv.eq.Zero.of.Lt
import Lemma.Rat.Sub_Div.eq.DivSubMul.of.Ne_0
open Nat Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {m n j : ℕ}
-- given
  (h : j < n) :
-- imply
  ⌈(m * n - j : α) / n⌉.toNat = m := by
-- proof
  rw [DivSubMul.eq.Sub_Div.of.Ne_0]
  ·
    rw [CeilSub.eq.Sub_Floor]
    simp [FloorDiv.eq.Zero.of.Lt h]
  ·
    simp
    apply Ne_0.of.Gt h


-- created on 2025-11-08
