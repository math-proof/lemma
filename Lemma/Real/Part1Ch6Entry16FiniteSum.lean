import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.Part1Ch6Entry16FiniteSum

/--
[Part1Ch6Entry16FiniteSum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry16FiniteSum.lean)
-/
@[path]
private lemma ramanujan_part1_ch6_entry16_finite_sum_general_eq
  [Field K]
-- given
  (a r x : K)
  (n : ℕ)
  (hax : ∀ k ∈ Finset.Icc 1 n, 1 - a * x ^ k ≠ 0)
  (hrx : ∀ k ∈ Finset.Icc 1 n, 1 - r * x ^ (k - 1) ≠ 0) :
-- imply
  ∑ k ∈ Finset.Icc 1 n, r ^ k / (1 - a * x ^ k) =
    (∑ k ∈ Finset.Icc 1 n, (a * r * x ^ k) ^ k / (1 - a * x ^ k)) +
      ∑ k ∈ Finset.Icc 1 n,
        a ^ (k - 1) *
          ((r * x ^ (k - 1)) ^ k - (r * x ^ (k - 1)) ^ (n + 1)) /
            (1 - r * x ^ (k - 1)) := by
-- proof
  apply Ramanujan.Part1Ch6.Entry16FiniteSum.ramanujan_part1_ch6_entry16_finite_sum_general a r x n hax hrx

/--
[Part1Ch6Entry16FiniteSum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry16FiniteSum.lean)
-/
@[path]
private lemma ramanujan_part1_ch6_entry16_finite_sum_eq
-- given
  (a r x : ℝ)
  (n : ℕ)
  (hn : 0 < n)
  (hax : ∀ k ∈ Finset.Icc 1 n, 1 - a * x ^ k ≠ 0)
  (hrx : ∀ k ∈ Finset.Icc 1 n, 1 - r * x ^ (k - 1) ≠ 0) :
-- imply
  ∑ k ∈ Finset.Icc 1 n, r ^ k / (1 - a * x ^ k) =
    (∑ k ∈ Finset.Icc 1 n, (a * r * x ^ k) ^ k / (1 - a * x ^ k)) +
      ∑ k ∈ Finset.Icc 1 n,
        a ^ (k - 1) *
          ((r * x ^ (k - 1)) ^ k - (r * x ^ (k - 1)) ^ (n + 1)) /
            (1 - r * x ^ (k - 1)) := by
-- proof
  apply Ramanujan.Part1Ch6.Entry16FiniteSum.ramanujan_part1_ch6_entry16_finite_sum a r x n hn hax hrx

-- created on 2026-10-10
