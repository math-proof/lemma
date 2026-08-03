import Lemma.Nat.Mod.eq.Sub_Mul_Div
import Lemma.Nat.Div.eq.FloorDiv
import Lemma.Nat.SubNatNat.eq.Sub
import Lemma.Nat.EqAddMul_Div
open Nat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {n d : ℕ} :
-- imply
  n % d = n - d * ⌊n / (d : α)⌋ := by
-- proof
  rw [← Div.eq.FloorDiv (α := α)]
  norm_cast
  have h := Mod.eq.Sub_Mul_Div (Z := ℕ) (n := n) (d := d)
  have := EqAddMul_Div (Z := ℕ) (n := n) (d := d)
  have h_le : d * (n / d) ≤ n := by omega
  rw [SubNatNat.eq.Sub, h, Nat.cast_sub h_le, Nat.cast_mul]


-- created on 2026-08-03
