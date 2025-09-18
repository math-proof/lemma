import Lemma.Algebra.Sub.ne.Zero.of.Ne
import Lemma.Algebra.CoeSub.eq.SubCoeS
import Lemma.Algebra.Ne.of.Sub.ne.Zero
import Lemma.Algebra.NeCoe_0.is.Ne_0
open Algebra


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
  rw [CoeSub.eq.SubCoeS.int] at h
  apply Ne.of.Sub.ne.Zero h


@[main]
private lemma nat
  [AddGroupWithOne R]
  [CharZero R]
  {a b : ℕ}
-- given
  (h : a ≠ b) :
-- imply
  (a : R) ≠ (b : R) := by
-- proof
  have h' : (a : ℤ) ≠ (b : ℤ) := by
    simp_all
  have := main (R := R) h'
  simp_all


-- created on 2025-03-30
-- updated on 2025-08-02
