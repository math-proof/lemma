import Mathlib
import Lemma.Fin.CardRothBox.eq.Prod_Add_1
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[roth_box_card_le_two_pow_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  {r : Fin m → ℕ}
-- given
  (hr : ∀ h, 0 < r h) :
-- imply
  Fintype.card (RothBox r) ≤ 2 ^ (∑ h, r h) := by
-- proof
  have succ_le_two_pow {n : ℕ} (hn : 0 < n) : n + 1 ≤ 2 ^ n := by
    induction n with
    | zero => omega
    | succ n ih =>
      if hn0 : n = 0 then
        subst n
        norm_num
      else
        calc
          _ ≤ 2 * (n + 1) := by omega
          _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 (ih (Nat.pos_of_ne_zero hn0))
          _ = 2 ^ (n + 1) := by rw [pow_succ]; ring
  rw [CardRothBox.eq.Prod_Add_1]
  calc
    _ ≤ ∏ h, 2 ^ r h := by
      gcongr with h
      exact succ_le_two_pow (hr h)
    _ = 2 ^ (∑ h, r h) := Finset.prod_pow_eq_pow_sum Finset.univ r 2


-- created on 2026-10-21
