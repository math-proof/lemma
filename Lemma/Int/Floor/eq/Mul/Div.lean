import sympy.functions.elementary.integers
import Lemma.Int.FDiv.eq.FloorDiv
open Int


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
-- given
  (n d : ℤ) :
-- imply
  (⌊n / (d : α)⌋ : α) = (n - n.fmod d) / d := by
-- proof
  rcases eq_or_ne d 0 with rfl | hd
  ·
    simp
  rw [← FDiv.eq.FloorDiv (α := α), eq_div_iff (by exact_mod_cast hd)]
  have e := Int.mul_fdiv_add_fmod n d
  have e' : n // d * d = n - n.fmod d := by
    rw [Int.mul_comm]
    linarith
  exact_mod_cast e'


-- created on 2026-09-27
