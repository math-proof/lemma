/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean -/

import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.PadicNumbers
/-!
# Rational places and completed fields

Source: arXiv:2607.14033, `pq-work-rank0-sha1.tex`, lines 237--240:

> Let M_Q be the set of all inequivalent normalised absolute values on Q.
> It consists of the ordinary absolute value, along with one non-archimedean
> absolute value for each prime number l.

`M_ℚ` is formalised as `Rat.Place` and `ℚ_v` as `CompletedField v`
(`ℝ` at infinity, `ℚ_[p]` at a prime), reusing
`Rat.AbsoluteValue.real` and `Rat.AbsoluteValue.padic`.
-/


namespace Rat

/-- Index for `M_ℚ`: inequivalent normalised absolute values on `ℚ`.

* `infinite` is the ordinary archimedean absolute value.
* `finite prime` is the `p`-adic absolute value for `prime = ⟨p, hp⟩`.
-/
inductive Place : Type where
  | infinite : Place
  | finite : (prime : Nat.Primes) → Place
  deriving DecidableEq

end Rat
