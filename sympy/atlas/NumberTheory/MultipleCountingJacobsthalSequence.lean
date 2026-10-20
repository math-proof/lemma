/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleCountingJacobsthalSequence.lean -/

import Mathlib.Order.Interval.Finset.Nat

namespace MetaMathlibExt

/-- Multiple-counting Jacobsthal sequence (concept `jis_sem_a69dabe897bb9ca4d746eba5`,
statements `jis_590ab02a1ec2a505ee5b9b61`, `jis_c5e526d097fecb5bdfc85583`):
`multipleCountingJacobsthalSequence x rho n` counts the multiples of `rho`
strictly between `x ^ n` and `x ^ (n + 1)`. The source studies `2 ≤ x` and
`2 ≤ rho`; the count itself is useful without those restrictions.

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL19/Cilasun/cila5.tex>. -/
def multipleCountingJacobsthalSequence (x rho n : ℕ) : ℕ :=
  ((Finset.Ioo (x ^ n) (x ^ (n + 1))).filter (fun k => rho ∣ k)).card

end MetaMathlibExt
