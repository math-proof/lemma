import Lemma.Bool.BoolAnd.eq.MulBoolS
import Lemma.Finset.Mul_Sum.eq.Sum_Mul
import Lemma.Finset.Sum.eq.Sum_MulBool
open Bool Finset


@[main]
private lemma main
  [DecidableEq ι]
  [Fintype ι]
  [NonAssocSemiring β]
  (A : Finset ι)
  (B : ι → Finset ι)
  (f : ι → ι → β) :
-- imply
  ∑ x, ∑ y, Bool.toNat (x ∈ A ∧ y ∈ B x) * f x y =
    ∑ x ∈ A, ∑ y ∈ B x, f x y := by
-- proof
  have h_rhs : ∑ x ∈ A, ∑ y ∈ B x, f x y = ∑ x, ∑ y, Bool.toNat (x ∈ A) * Bool.toNat (y ∈ B x) * f x y := calc
    _ = ∑ x, Bool.toNat (x ∈ A) * (∑ y ∈ B x, f x y) := by rw [Sum.eq.Sum_MulBool]
    _ = ∑ x, Bool.toNat (x ∈ A) * ∑ y, Bool.toNat (y ∈ B x) * f x y := by
      congr 1
      funext x
      rw [Sum.eq.Sum_MulBool]
    _ = ∑ x, ∑ y, Bool.toNat (x ∈ A) * Bool.toNat (y ∈ B x) * f x y := by
      congr 1
      funext x
      rw [Mul_Sum.eq.Sum_Mul]
      congr 1
      funext y
      by_cases hx : x ∈ A <;> by_cases hy : y ∈ B x <;> simp [hx, hy]
  have h_lhs : ∑ x, ∑ y, Bool.toNat (x ∈ A ∧ y ∈ B x) * f x y = ∑ x, ∑ y, Bool.toNat (x ∈ A) * Bool.toNat (y ∈ B x) * f x y := by
    congr 1
    funext x
    congr 1
    funext y
    rw [BoolAnd.eq.MulBoolS, Nat.cast_mul]
  rw [h_lhs, h_rhs]


-- created on 2018-05-01
-- updated on 2026-08-06
