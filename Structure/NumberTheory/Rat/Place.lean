/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean -/

import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.PadicNumbers
import Def.NumberTheory.Rat.Place
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

/-- Bundled carrier together with the `NormedField` / `CompleteSpace`
instances needed for the completed field `ℚ_v`.

Using a bundle avoids a direct dependent family `Place → Type` returning
`Padic p`, which loses the local `Fact` dictionary and causes kernel
declaration mismatches in projected instances. Instance-valued fields use
bracket syntax so the bundle itself carries the instances. -/
structure CompletedFieldBundle where
  carrier : Type
  [normedField : NormedField carrier]
  [completeSpace : CompleteSpace carrier]

end Place
end Rat
