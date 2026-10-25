/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean -/

import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.PadicNumbers
import Structure.NumberTheory.Rat.Place
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

instance : CoeSort CompletedFieldBundle Type where
  coe B := B.carrier

end Place
end Rat
