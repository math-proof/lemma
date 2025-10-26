import Lemma.Int.Sub.ne.Zero.of.Ne
import Lemma.Int.CoeSub.eq.SubCoeS
import Lemma.Int.Ne.of.Sub.ne.Zero
import Lemma.Int.NeCoe_0.is.Ne_0
open Int


@[main]
private lemma main
  [AddGroupWithOne R]
  [CharZero R]
  {a b : ℤ}
-- given
  (h : a ≠ b) :
-- imply
  (a : R) ≠ (b : R) := by
-- proof
  have h := Sub.ne.Zero.of.Ne h
  have h := NeCoe_0.of.Ne_0 h (α := R)
  rw [CoeSub.eq.SubCoeS] at h
  apply Ne.of.Sub.ne.Zero h


-- created on 2025-03-30
-- updated on 2025-10-16
