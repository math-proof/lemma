import Mathlib
import Instance.Analysis.Appendix_B_1.Part3
/-!
# Analysis I, Appendix B.1: The decimal representation of natural numbers

Am implementation of the decimal representation of Mathlib's natural numbers {lean}`ℕ`.

This is separate from the way decimal numerals are already represenated in Mathlib via the {name}`OfNat` typeclass.
-/


namespace AppendixB

theorem PosintDecimal.ten_eq_ten : (mk' 1 [0] (by decide):ℕ) = 10 := by
  decide

theorem PosintDecimal.digit_eq {d:Digit} (h: d ≠ 0) : (mk' d [] h:ℕ) = d := by
  unfold toNat
  simp only [mk']
  have hlen : ((d :: []) : List Digit).length = 1 := by simp
  simp [hlen, pow_zero]
  set_option backward.isDefEq.respectTransparency false in
    simp [Fintype.card_fin, one_mul]

theorem PosintDecimal.pos (p:PosintDecimal) : 0 < (p:ℕ) := by
  simp [toNat]
  calc
    _ < (p.head:ℕ) * 10 ^ (p.digits.length - 1) := by
      have := p.head_ne_zero'
      positivity
    _ ≤ _ := by
      have := p.length_pos
      set a : Fin p.digits.length := ⟨ p.digits.length - 1, by omega ⟩
      convert Finset.single_le_sum _ (Finset.mem_univ a)
      . simp [a, head, List.head_eq_getElem]
      . infer_instance
      grind

end AppendixB
