/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/RightDownDiagonalSequences.lean -/


import sympy.atlas.Combinatorics.Enumerative.RightDownDiagonalSequences

namespace MetaMathlibExt

example (k : ℕ) (hk : 1 ≤ k) :
    IsRightDownDiagonalFamily k (fun _ _ => 0) := by
  refine ⟨hk, ?_⟩
  intro j n hn
  simp

/-- At order four, the recurrence has coefficients `5, -6, 1` and lags
one, two, and three, respectively. -/
example (A : Fin 6 → ℕ → ℤ) :
    IsRightDownDiagonalFamily 4 A ↔
      ∀ j n, 3 ≤ n →
        A j n = 5 * A j (n - 1) + (-6) * A j (n - 2) + A j (n - 3) := by
  have hchoose : Nat.choose 4 2 = 6 := by decide
  simp [IsRightDownDiagonalFamily, rightDownDiagonalCoefficient,
    Finset.sum_range_succ, hchoose, Nat.sub_sub]

end MetaMathlibExt
