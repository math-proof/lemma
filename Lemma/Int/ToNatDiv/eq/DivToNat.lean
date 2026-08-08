import Lemma.Int.EqToNat_0.of.Lt_0
open Int


@[main]
private lemma main
-- given
  (n : ℤ)
  (d : ℕ) :
-- imply
  (n / d).toNat = n.toNat / d := by
-- proof
  if hn : 0 ≤ n then
    grind
  else
    have hnneg : n < 0 := lt_of_not_ge hn
    rw [EqToNat_0.of.Lt_0 hnneg, Nat.zero_div]
    if hd : d = 0 then
      simp [hd]
    else
      apply EqToNat_0.of.Lt_0 (Int.ediv_neg_of_neg_of_pos hnneg ?_)
      apply Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd)


-- created on 2026-08-08
