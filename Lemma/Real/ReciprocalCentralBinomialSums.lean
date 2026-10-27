import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Data.Nat.Choose.ReciprocalCentralBinomialSums

/--
[ReciprocalCentralBinomialSums](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Series/ReciprocalCentralBinomialSums.lean)
-/
@[path]
private lemma reciprocal_central_binomial_sums_is :
-- imply
  HasSum
    (fun m : ℕ =>
      1 / (((m + 1 : ℕ) : ℝ) * (Nat.choose (2 * (m + 1)) (m + 1) : ℝ)))
    (Real.pi * Real.sqrt 3 / 9) ∧
    HasSum
      (fun m : ℕ => 1 / (Nat.choose (2 * (m + 1)) (m + 1) : ℝ))
      (1 / 3 + 2 * Real.pi / (9 * Real.sqrt 3)) ∧
    HasSum
      (fun m : ℕ =>
        1 /
          ((((m + 1 : ℕ) : ℝ) ^ 2) *
            (Nat.choose (2 * (m + 1)) (m + 1) : ℝ)))
      (Real.pi ^ 2 / 18) := by
-- proof
  apply MetaMathlibExt.reciprocal_central_binomial_sums

-- created on 2026-10-10
