import Lemma.Int.ToNatDiv.eq.DivToNat
open Int


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d ≥ 0) :
-- imply
  (n / d).toNat = n.toNat / d.toNat := by
-- proof
  if hd0 : d = 0 then
    simp [hd0]
  else
    rw [← Int.toNat_of_nonneg (le_of_lt (lt_of_le_of_ne h (Ne.symm hd0)))]
    exact ToNatDiv.eq.DivToNat n d.toNat


-- created on 2026-08-08
