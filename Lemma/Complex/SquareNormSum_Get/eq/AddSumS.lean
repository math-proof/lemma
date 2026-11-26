import Instance.Data.Nat.Fun
import Notation.Algebra.Power
import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {a : ℕ → ℂ} :
-- imply
  ‖∑ i < n, a[i]‖² = ∑ i < n, ‖a[i]‖² + ∑ i < n, ∑ j < i, 2 * (~a[i] * a[j]).re := by
-- proof
  simp only [Nat.Iio_eq_range]
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    have key : (~a[n] * (Finset.range n).sum (fun j => a[j])).re = (Finset.range n).sum (fun j => (~a[n] * a[j]).re) := by
      rw [Finset.mul_sum, Complex.re_sum]
    rw [Complex.sq_norm, Complex.normSq_add, ← Complex.sq_norm, ← Complex.sq_norm, ih, ← Finset.mul_sum, ← key, mul_comm ((Finset.range n).sum (fun j => a[j]))]
    ring


-- created on 2023-06-24
-- updated on 2026-11-26
