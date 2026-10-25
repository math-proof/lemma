import Mathlib
import sympy.Basic
import Def.Combinatorics.Enumerative.EulerSeidelMatrix
open MetaMathlibExt


namespace MetaMathlibExt

/--
[eulerSeidelMatrix_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerSeidelMatrix.lean)
-/
@[path]
lemma eulerSeidelMatrix_eq_sum
  [AddCommMonoid M]
  {a : ℕ → M}
  {n k : ℕ} :
-- imply
  eulerSeidelMatrix a n k = ∑ i ∈ Finset.range (k + 1), k.choose i • a (n + i) := by
-- proof
  induction k generalizing n with
  | zero =>
    have h0 : eulerSeidelMatrix a n 0 = a n := rfl
    have h01 : (0 : ℕ) + 1 = 1 := rfl
    rw [h0, h01, Finset.sum_range_one, Nat.choose_self, one_nsmul, Nat.add_zero]
  | succ k ih =>
    have hdef : eulerSeidelMatrix a n k.succ
      = eulerSeidelMatrix a n k + eulerSeidelMatrix a (n + 1) k := rfl
    have hT : (∑ i ∈ Finset.range (k.succ + 1), (k.succ).choose i • a (n + i))
      = (∑ i ∈ Finset.range (k + 1), (k + 1).choose (i + 1) • a (n + (i + 1)))
        + a n := by
      rw [Finset.sum_range_succ']
      simp only [Nat.succ_eq_add_one]
      rw [show (k + 1).choose 0 • a (n + 0) = a n from by
        rw [Nat.choose_zero_right, one_nsmul, Nat.add_zero]]
    have hsplit :
      (∑ i ∈ Finset.range (k + 1), (k + 1).choose (i + 1) • a (n + (i + 1)))
      = (∑ i ∈ Finset.range (k + 1), k.choose i • a (n + (i + 1)))
        + (∑ i ∈ Finset.range (k + 1), k.choose (i + 1) • a (n + (i + 1))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Nat.choose_succ_succ', add_nsmul]
    have hM1 : (∑ i ∈ Finset.range (k + 1), k.choose i • a (n + (i + 1)))
      = ∑ i ∈ Finset.range (k + 1), k.choose i • a (n + 1 + i) := by
      apply Finset.sum_congr rfl
      intro i _
      have e : n + (i + 1) = n + 1 + i := by omega
      rw [e]
    have hM2 : (∑ i ∈ Finset.range (k + 1), k.choose (i + 1) • a (n + (i + 1)))
      = ∑ i ∈ Finset.range k, k.choose (i + 1) • a (n + (i + 1)) := by
      have hvan : k.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [Finset.sum_range_succ, hvan, zero_nsmul, add_zero]
    have hS1 : (∑ i ∈ Finset.range (k + 1), k.choose i • a (n + i))
      = (∑ i ∈ Finset.range k, k.choose (i + 1) • a (n + (i + 1))) + a n := by
      rw [Finset.sum_range_succ']
      rw [show k.choose 0 • a (n + 0) = a n from by
        rw [Nat.choose_zero_right, one_nsmul, Nat.add_zero]]
    rw [hdef, ih, ih, hT, hsplit, hS1, hM1, hM2]
    ac_rfl

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
