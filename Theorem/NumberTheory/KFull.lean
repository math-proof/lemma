/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean -/

import Mathlib.Data.Nat.Factorization.Basic
import Def.NumberTheory.KFull
/-!
# `k`-full numbers

Following Li–Wang–Wang–Yi ("Some ergodic theorems over squarefree numbers and
squarefull numbers", Acta Arith. 221 (2025), no. 2, 117-140): for an integer
`k ≥ 2`, a natural number `n` is `k`-full if `p ^ k ∣ n` for every prime factor
`p` of `n`.

The source works with positive naturals: `0` is excluded and `1` is `k`-full
vacuously (it has no prime factors). `Nat.IsKFull` below is total in `k`, so its
values at `k = 0` and `k = 1` are documented and proved explicitly
(`Nat.isKFull_k_eq_zero`, `Nat.isKFull_k_eq_one`); source-facing consequences
(such as `Nat.isKFull_of_two_le`) assume `2 ≤ k`. The `k = 2` specialization
(`Nat.isKFull_two`) is the squarefull/powerful case.

The function `Nat.powerfulPart` keeps exactly the prime-power factors whose
exponents are at least two.
-/


namespace Nat

@[simp] theorem powerfulPart_zero : powerfulPart 0 = 1 := by
  unfold powerfulPart
  simp

@[simp] theorem powerfulPart_one : powerfulPart 1 = 1 := by
  unfold powerfulPart
  simp

end Nat
