/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/SimsekNumber.lean -/


import Def.NumberTheory.SimsekNumber
import Lemma.Nat.SimsekNumber


namespace MetaMathlibExt

/-- The definition sums exactly over `Finset.range (k + 1)`. -/
example (n k : Nat) (lam : ℂ) :
    simsekNumber n k lam =
      ((k.factorial : ℂ))⁻¹ *
        ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * (((j : ℂ) ^ n) * (lam ^ j)) :=
  rfl

/-- Lower endpoint `j = 0`: with `k = 0` only that term remains. -/
example (n : Nat) (lam : ℂ) : simsekNumber n 0 lam = (0 : ℂ) ^ n :=
  simsekNumber_zero_k n lam

/-- Upper endpoint `j = k`: with `k = 1` and `n = 1` the top term gives `lam`. -/
example (lam : ℂ) : simsekNumber 1 1 lam = lam := by
  simp [simsekNumber, Finset.sum_range_succ]

/-- Small value at `(n, k) = (0, 0)`. -/
example (lam : ℂ) : simsekNumber 0 0 lam = 1 :=
  simsekNumber_zero_zero lam

/-- Small value at `(n, k) = (1, 2)`: `(lam + lam ^ 2)`. -/
example (lam : ℂ) : simsekNumber 1 2 lam = lam + lam ^ 2 := by
  unfold simsekNumber
  simp [Finset.sum_range_succ]
  ring

end MetaMathlibExt
