/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean -/

import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Tame and wild ramification at a prime

Let `S` be an `R`-algebra and `q` a prime ideal of `S`. We say `q` is
*tamely ramified* over `R` if the residue-field extension
`(q.under R).ResidueField → q.ResidueField` is separable and the residue
characteristic does not divide the ramification index `q.ramificationIdx R`.
*Wild ramification* is the logical complement of tame ramification.

The residue-field algebra is the canonical one coming from
`Localization.AtPrime.algebraOfLiesOver (q.under R) q`, installed locally
inside `Algebra.IsResidueSeparableAt`, so the tame/wild predicates require no
localization-algebra hypotheses from callers.

## Main definitions

* `Algebra.IsResidueSeparableAt R q`: residue separability at `q`.
* `Algebra.IsTamelyRamifiedAt R q`: tame ramification at `q`.
* `Algebra.IsWildlyRamifiedAt R q`: wild ramification at `q`, defined as
  `¬ Algebra.IsTamelyRamifiedAt R q`.

## Main results

* `Algebra.isTamelyRamifiedAt_iff`: unfolding of tame ramification.
* `Algebra.isWildlyRamifiedAt_iff_char_dvd`: under residue separability,
  wild ramification holds iff the residue characteristic divides the
  ramification index.
* `Algebra.isWildlyRamifiedAt_of_char_dvd`: wild ramification follows from the
  residue characteristic dividing the ramification index, with no separability
  hypothesis.
* `Algebra.isWildlyRamifiedAt_of_not_isResidueSeparableAt`: wild ramification
  follows from residue inseparability.
* `Algebra.isTamelyRamifiedAt_of_isUnramifiedAt`: unramified primes are tame.
* `Algebra.isTamelyRamifiedAt_iff_isSeparable_of_charZero`: in residue
  characteristic zero, tame ramification is equivalent to residue separability.
-/

namespace Algebra

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (q : Ideal S) [q.IsPrime]

/-- Residue separability at `q`: the residue-field extension
`(q.under R).ResidueField → q.ResidueField` is separable, using the canonical
localization algebra `Localization.AtPrime.algebraOfLiesOver (q.under R) q`
installed locally, so callers supply no localization-algebra instances. -/
def IsResidueSeparableAt : Prop :=
  letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q;
    Algebra.IsSeparable (q.under R).ResidueField q.ResidueField

/-- A prime `q` of `S` is *tamely ramified* over `R` if the residue-field
extension is separable and the residue characteristic does not divide the
ramification index. -/
def IsTamelyRamifiedAt : Prop :=
  IsResidueSeparableAt R q ∧ ¬ ringChar q.ResidueField ∣ q.ramificationIdx R

/-- A prime `q` of `S` is *wildly ramified* over `R` if it is not tamely
ramified over `R`. -/
def IsWildlyRamifiedAt : Prop :=
  ¬ IsTamelyRamifiedAt R q
end Algebra
