/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TelescopicSequence.lean -/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Group.Submonoid.Basic


namespace MetaMathlibExt

/-- Prefix gcds `d_j` of a sequence `G ∈ ℕ₀^k`.

Computes `Nat.gcd` folded over the first `j` entries, starting from `0`
(`d_0 = 0`). Source identifiers: `jis_0047f665dcff445f0a87ef54`,
`jis_e21a41021ffe77e39d11f0e2`, `jis_480413725b64a0d49eabe98d`. -/
def telescopicGcd (G : List ℕ) (j : ℕ) : ℕ :=
  (G.take j).foldl Nat.gcd 0

/-- Successive gcd quotient `c_j = d_{j-1} / d_j` of `G`.

Uses `Nat` truncated division. Convention: when a whole prefix is zero, so
`d_j = 0`, `c_j` degenerates to `0`; the source usage always assumes `g₁ > 0`
or `gcd(G) = 1`, avoiding this case. Reproduces the source values, e.g.
`(6, 5, 11, 2)` for `(660, 550, 352, 50, 201)` and `(3, 1)` for `(3, 4, 5)`.
Source identifiers: `jis_0047f665dcff445f0a87ef54`,
`jis_e21a41021ffe77e39d11f0e2`, `jis_480413725b64a0d49eabe98d`,
`jis_ce7ca3b188a2135cbe5b0077`. -/
def telescopicC (G : List ℕ) (j : ℕ) : ℕ :=
  telescopicGcd G (j - 1) / telescopicGcd G j

/-- `G ∈ ℕ₀^k` is telescopic when `k ≥ 2`, `g₁ + g₂ > 0`, and
`c_j * g_j ∈ ⟨G_{j-1}⟩` for `2 ≤ j ≤ k`.

Here `G.getD (j - 1) 0` is `g_j` (the `j`-th entry, `1`-indexed) and
`{x | x ∈ G.take (j - 1)}` is the set of the first `j - 1` entries generating
`⟨G_{j-1}⟩` as an additive submonoid. Source identifiers:
`jis_480413725b64a0d49eabe98d`, `jis_5da42b058565b53729b9afa2`,
`jis_a68226f2d394da5aef17cdad`, `jis_ce7ca3b188a2135cbe5b0077`,
`jis_e21a41021ffe77e39d11f0e2`. -/
def IsTelescopic (G : List ℕ) : Prop :=
  2 ≤ G.length ∧
    0 < G.getD 0 0 + G.getD 1 0 ∧
      ∀ j : ℕ, 2 ≤ j → j ≤ G.length →
        telescopicC G j * G.getD (j - 1) 0 ∈
          AddSubmonoid.closure {x | x ∈ G.take (j - 1)}

end MetaMathlibExt
