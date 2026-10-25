/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean -/

import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.PadicNumbers
import Inductive.NumberTheory.Rat.Place
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

/-- Normalised real-valued absolute value attached to a place.

Reuses `Rat.AbsoluteValue.real` at infinity and `Rat.AbsoluteValue.padic`
at a finite prime. `Rat.AbsoluteValue.padic` takes `[Fact p.Prime]`,
so the proof in `prime` is turned into a local `Fact` dictionary. -/
noncomputable def absoluteValue : Place → AbsoluteValue ℚ ℝ
  | .infinite => Rat.AbsoluteValue.real
  | .finite prime =>
    haveI : Fact prime.1.Prime := ⟨prime.2⟩
    Rat.AbsoluteValue.padic prime.1

end Place
end Rat
