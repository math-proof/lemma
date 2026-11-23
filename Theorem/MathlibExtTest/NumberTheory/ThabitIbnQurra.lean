/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ThabitIbnQurra.lean -/
module

public import Theorem.Nat.ThabitIbnQurra
open scoped BigOperators

public section

-- The classical `n = 2` case gives the amicable pair `220` and `284`.
example :
    220 < 284 ∧
      ∑ d ∈ Nat.properDivisors 220, d = 284 ∧
      ∑ d ∈ Nat.properDivisors 284, d = 220 := by
  simpa using
    (MetaMathlibExt.thabit_ibn_qurra 2 11 5 71 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide))

