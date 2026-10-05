import Mathlib.Data.Int.Interval
import sympy.Basic


@[main]
private lemma main
  {α : Type*} [AddCommGroup α]
  {x : ℤ → α}
  {i n : ℤ}
-- given
  (h : i ≤ n) :
-- imply
  ∑ k ∈ Finset.Ico i (n + 1), (x (k + 1) - x k) = x (n + 1) - x i := by
-- proof
  set d : ℕ := (n + 1 - i).toNat with hd
  have hdi : (i + d : ℤ) = n + 1 := by omega
  have hsum :
      ∑ j ∈ Finset.range d, (x (i + (j + 1)) - x (i + j)) =
        x (i + d) - x i := by
    induction d with
    | zero =>
      simp
    | succ d ih =>
      rw [Finset.sum_range_succ, ih]
      simp
  rw [Int.Ico_eq_finset_map i (n + 1), Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply]
  have hr : (n + 1 - i).toNat = d := by omega
  rw [hr, show n + 1 = i + d from hdi.symm]
  convert hsum using 3
  ring_nf


-- created on 2020-03-24
