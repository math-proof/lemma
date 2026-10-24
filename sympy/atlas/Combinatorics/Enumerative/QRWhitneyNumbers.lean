/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean -/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# (q, r)-Whitney numbers of the first and second kind

Formalizes the q-integer as a finite geometric sum and the two triangular
recurrence arrays from the source. Concept `jis_sem_1510537ed21edced61e4c308`.
Source statement IDs: `jis_b6c9b8526668212b3d271ce0`, `jis_bfbfab3b67f1c02f167938f1`,
`jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`, `jis_dd5f8c454fc5760fb197859b`.
Original definitions via q-boson operators (`qw1`, `qw2`) are represented here by
the proved triangular recurrences (`identity4`, `identity5`) as the executable
definitions. The first-kind recurrence divides by `q ^ n`, so its API explicitly
assumes `q ≠ 0`; this avoids Lean's totalized inverse assigning unintended values
at the singular parameter `q = 0`.
-/

namespace MetaMathlibExt

namespace QRWhitney

/-- q-integer `[n]_q` as the finite geometric sum `∑ i in range n, q ^ i`.
Concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. Avoids any singularity at `q = 1`. -/
def qBrack (q : ℂ) (n : ℕ) : ℂ :=
  Finset.sum (Finset.range n) (fun i => q ^ i)

/-- (q, r)-Whitney numbers of the first kind `w_{m,r,q}(n, k)`, defined by the
triangular recurrence `identity4` split at `k = 0` vs `k + 1`.
Concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
noncomputable def whitneyFirst (m r q : ℂ) [NeZero q] : ℕ → ℕ → ℂ
  | 0 => fun | 0 => 1 | _ + 1 => 0
  | n + 1 => fun
    | 0 => (q ^ n)⁻¹ * (0 - (m * qBrack q n + r) * whitneyFirst m r q n 0)
    | k + 1 =>
      (q ^ n)⁻¹ *
        (whitneyFirst m r q n k -
          (m * qBrack q n + r) * whitneyFirst m r q n (k + 1))

/-- (q, r)-Whitney numbers of the second kind `W_{m,r,q}(n, k)`, defined by the
triangular recurrence `identity5` split at `k = 0` vs `k + 1`.
Concept `jis_sem_1510537ed21edced61e4c308`; statements `jis_b6c9b8526668212b3d271ce0`,
`jis_bfbfab3b67f1c02f167938f1`, `jis_bfd5e69c1279fc0a6f4ff0e3`, `jis_ceb0c2289757d5617de10695`,
`jis_dd5f8c454fc5760fb197859b`. -/
def whitneySecond (m r q : ℂ) : ℕ → ℕ → ℂ
  | 0 => fun | 0 => 1 | _ + 1 => 0
  | n + 1 => fun
    | 0 => r * whitneySecond m r q n 0
    | k + 1 =>
      q ^ k * whitneySecond m r q n k +
        (m * qBrack q (k + 1) + r) * whitneySecond m r q n (k + 1)
end QRWhitney
end MetaMathlibExt
