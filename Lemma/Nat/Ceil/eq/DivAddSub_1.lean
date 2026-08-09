import Lemma.Int.Ceil.eq.FloorDivSub_Sign
import Lemma.Int.EqSign_1.of.Gt_0
import Lemma.Nat.Div.eq.FloorDiv
import Lemma.Nat.Gt_0.of.Ne_0
import sympy.Basic
open Int Bool Nat Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
-- given
  (n d : ℕ) :
-- imply
  ⌈n / (d : α)⌉ = (d - 1 + n) / d := by
-- proof
  suffices ⌈(n : ℤ) / ((d : ℤ) : α)⌉ = (d - 1 + n) / d by
    simpa using this
  rw [Ceil.eq.FloorDivSub_Sign]
  if h_d : d = 0 then
    rw [h_d]
    norm_num
  else
    have h_d_pos := Gt_0.of.Ne_0 h_d
    have h_sign := EqSign_1.of.Gt_0 (show (0 : ℤ) < d from mod_cast h_d_pos)
    have h_main : ⌊((d : ℤ) + (n : ℤ) - 1 : α) / ((d : ℤ) : α)⌋ = ↑((d - 1 + n) / d) := calc
      _ = ⌊((d - 1 + n : ℕ) : α) / (d : α)⌋ := by
        refine congrArg Int.floor ?_
        push_cast
        field_simp
        ring_nf
        norm_cast
        omega
      _ = ↑((d - 1 + n) / d) := by
        symm
        apply Div.eq.FloorDiv
    rw [h_sign]
    simpa [Int.cast_one] using h_main.trans (by grind)


-- created on 2026-08-09
