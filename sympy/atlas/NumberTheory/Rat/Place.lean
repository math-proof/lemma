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

instance : CoeSort CompletedFieldBundle Type where
  coe B := B.carrier

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

noncomputable instance (v : Place) : NormedField (CompletedField v) :=
  (bundle v).normedField

instance (v : Place) : CompleteSpace (CompletedField v) :=
  (bundle v).completeSpace

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
