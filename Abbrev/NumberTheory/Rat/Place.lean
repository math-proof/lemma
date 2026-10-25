/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean -/

import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.PadicNumbers
import Instance.NumberTheory.Rat.Place
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

namespace Place

/-- Bundle selection by place. Exactly `ℝ` at infinity and `Padic p` at
a prime. `noncomputable abbrev` so reduction exposes standard real and
`p`-adic structures. -/
noncomputable abbrev bundle : Place → CompletedFieldBundle
  | .infinite => ⟨ℝ⟩
  | .finite prime =>
    haveI : Fact prime.1.Prime := ⟨prime.2⟩
    ⟨Padic prime.1⟩

/-- The completed field `ℚ_v` attached to a place `v`. Coerced from the
selected bundle. -/
noncomputable abbrev CompletedField (v : Place) : Type :=
  (bundle v : Type)

end Place
end Rat
