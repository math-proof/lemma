/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamanujanSum.lean -/

/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun, Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang
-/

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Ramanujan sums

This file defines the classical Ramanujan sum using the standard additive character of `ZMod n`.

## Main definitions

* `MetaMathlibExt.ramanujanSum`

## Main statements

* `MetaMathlibExt.ramanujanSum_zero`
* `MetaMathlibExt.ramanujanSum_modulus_one`
* `MetaMathlibExt.ramanujanSum_add_mul_modulus`

## References

The definition follows the convention
`c_n(t) = ∑_{a ∈ (ZMod n)ˣ} e_n(a * t)`. Its Lean representation is adapted from the
Apache-2.0 licensed `ramanujanSum` declaration in
[UW Lean Pool](https://github.com/Vilin97/lean-pool), revision
`faa8c032722c955187fae103c96e8e93066f4592`, in `LeanPool.LatticeTriangle.Solution`.
-/

namespace MetaMathlibExt

/-- The Ramanujan sum of modulus `n` at `t`, expressed through the standard additive
character on `ZMod n`.

The assumption `[NeZero n]` expresses the usual requirement that the natural-number
modulus be positive. -/
noncomputable def ramanujanSum (n : ℕ) [NeZero n] (t : ℤ) : ℂ :=
  ∑ a : (ZMod n)ˣ, ZMod.stdAddChar ((a : ZMod n) * (t : ZMod n))
end MetaMathlibExt
