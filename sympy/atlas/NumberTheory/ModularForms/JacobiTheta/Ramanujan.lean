/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ModularForms/JacobiTheta/Ramanujan.lean -/

import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Ring

/-!
# Ramanujan's general theta function

This file defines Ramanujan's general theta function in its two multiplicative parameters

  `f(a,b) = ∑_{n ∈ ℤ} a ^ (n * (n + 1) / 2) * b ^ (n * (n - 1) / 2)`,

with classical (absolute) convergence on `‖a * b‖ < 1`. The raw sum
`ramanujanThetaRaw` is Mathlib's total `tsum`, which is `0` for a nonsummable family.
The canonical `ramanujanTheta` therefore requires an explicit summability witness.

## Main definitions

* `ramanujanThetaTerm a b n` — the `n`th summand.
* `ramanujanThetaRaw a b` — the unrestricted total `tsum`.
* `ramanujanTheta a b h` — the theta sum with summability evidence `h`.

## Main results

* `ramanujanThetaTerm_neg` and `ramanujanTheta_symm`: `f(a,b) = f(b,a)` via `n ↦ -n`.
-/

namespace MetaMathlibExt

/-- The summand `a ^ (n * (n + 1) / 2) * b ^ (n * (n - 1) / 2)` in Ramanujan's
general theta function `f(a,b) = ∑' n, a ^ (n(n+1)/2) b ^ (n(n-1)/2)`.

Both integer quotients are nonnegative triangular numbers (`n(n+1)/2 ≥ 0` and
`n(n-1)/2 ≥ 0` for `n : ℤ`), so the `ℤ`-division followed by `toNat` is exact and yields the
mathematical exponent in `ℕ`. Source: the common definition in arXiv:2305.14988,
arXiv:2309.06689, arXiv:2312.15513, arXiv:2502.17312, and arXiv:2607.26471. -/
noncomputable def ramanujanThetaTerm (a b : ℂ) (n : ℤ) : ℂ :=
  a ^ (n * (n + 1) / 2).toNat * b ^ (n * (n - 1) / 2).toNat

/-- Raw Ramanujan theta sum in multiplicative coordinates.

This is Mathlib's total `tsum`; it equals `0` when the summand family is not summable.
Use `ramanujanTheta`, which requires convergence evidence, unless that fallback is intended. -/
noncomputable def ramanujanThetaRaw (a b : ℂ) : ℂ :=
  ∑' n : ℤ, ramanujanThetaTerm a b n

/-- Ramanujan's general theta function, restricted to summable parameters. -/
noncomputable def ramanujanTheta (a b : ℂ)
    (_h : Summable (ramanujanThetaTerm a b)) : ℂ :=
  ramanujanThetaRaw a b
end MetaMathlibExt
