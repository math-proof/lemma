/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/PolyInitialExpansion.lean -/


import Mathlib.Data.Nat.Choose.Sum
import Lemma.Finset.Enumerative.PolyInitialExpansion


namespace MetaMathlibExt

-- Chen's expansion specializes to the signed Stirling-number sum.
example (t : ℕ) :
    ∑ m ∈ Finset.range (t + 1),
      (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) * (Nat.stirlingSecond t m : ℝ) =
        (-1 : ℝ) ^ t := by
  symm
  simpa using
    (chen_stirlingSecond_expansion t (fun _ s => (-1 : ℝ) ^ s) (by
      intro m s
      rw [pow_succ]
      ring))

-- The polynomial expansion specializes to the binomial theorem at `-1`.
example (n : ℕ) (x : ℝ) :
    ∑ m ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) * generalizedStirlingSecond n m x =
        (x - 1) ^ n := by
  calc
    _ = ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℝ) * x ^ k * (-1 : ℝ) ^ (n - k) := by
      symm
      simpa using
        (poly_initial_expansion n x (fun _ s => (-1 : ℝ) ^ s) (by
          intro m s
          rw [pow_succ]
          ring))
    _ = (x + (-1 : ℝ)) ^ n := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (x - 1) ^ n := by
      simp [sub_eq_add_neg]

end MetaMathlibExt
