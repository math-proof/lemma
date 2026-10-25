/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean -/

import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.PadicNumbers
import Instance.NumberTheory.Rat.Place.Part2
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

/-- Canonical ring embedding `ℚ →+* ℚ_v`.

At infinity this is `Rat.castHom ℝ`; at a finite prime it is
`Rat.castHom (Padic p)` under the local `Fact p.Prime` instance. -/
noncomputable def embedding : (v : Place) → ℚ →+* CompletedField v
  | .infinite => Rat.castHom ℝ
  | .finite prime =>
    haveI : Fact prime.1.Prime := ⟨prime.2⟩
    Rat.castHom (Padic prime.1)

/-- Canonical ring hom from `WithAbs v.absoluteValue` into `v.CompletedField`.

`WithAbs.equiv` identifies the elements of the source with `ℚ`, allowing
`embedding v` to serve as the underlying hom and as the bridge for the norm
identity. -/
noncomputable def withAbsEmbedding (v : Place) :
    WithAbs (v.absoluteValue) →+* CompletedField v :=
  (embedding v).comp (WithAbs.equiv (v.absoluteValue)).toRingHom

end Place
end Rat
