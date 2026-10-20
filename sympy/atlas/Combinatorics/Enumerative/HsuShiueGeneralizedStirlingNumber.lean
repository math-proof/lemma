/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/HsuShiueGeneralizedStirlingNumber.lean -/

import Mathlib.Analysis.RCLike.Basic

/-!
Hsu-Shiue generalized Stirling numbers S(n, k; alpha, beta, r),
following the JIS source (source statement jis_7e7402faeeffb59e829d97bc).

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL15/Schork/schork2.tex>.
-/

namespace MetaMathlibExt

variable {K : Type*} [RCLike K]

/-- Generalized factorial with increment `alpha`: `(z | alpha) 0 = 1` and
for `n >= 1`, `(z | alpha) n = z (z - alpha) ... (z - n * alpha + alpha)`,
via the recursion `F (n + 1) = F n * (z - n * alpha)`
(source statement jis_7e7402faeeffb59e829d97bc). -/
noncomputable def generalizedFallingFactorial (z alpha : K) : Nat → K
  | 0 => 1
  | n + 1 => generalizedFallingFactorial z alpha n * (z - (n : K) * alpha)

/-- Characterization of the Hsu-Shiue family `S(n, k; alpha, beta, r)`:
the parameters `alpha, beta, r` (real or complex, via `RCLike`) are not all
zero; the initial column is `S n 0 = (r | alpha) n`; and the recurrence
`S (n + 1) (k + 1) = S n k + ((k + 1) * beta - n * alpha + r) * S n (k + 1)`
holds, which is the source recurrence stated at indices where `k - 1`
is defined. The triangular-support condition `S n k = 0` for `n < k`
fixes the otherwise unconstrained initial row (source statement
`jis_7e7402faeeffb59e829d97bc`). -/
def IsHsuShiueFamily (S : Nat → Nat → K) (alpha beta r : K) : Prop :=
  ¬ (alpha = 0 ∧ beta = 0 ∧ r = 0) ∧
    (∀ n, S n 0 = generalizedFallingFactorial r alpha n) ∧
      (∀ n k, n < k → S n k = 0) ∧
        ∀ n k, S (n + 1) (k + 1) =
          S n k + (((k : K) + 1) * beta - (n : K) * alpha + r) * S n (k + 1)

end MetaMathlibExt
