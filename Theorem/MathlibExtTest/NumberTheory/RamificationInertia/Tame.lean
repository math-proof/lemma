/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/RamificationInertia/Tame.lean -/


import Def.NumberTheory.RamificationInertia.Tame
import Lemma.Int.RamificationInertia.Tame
variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (q : Ideal S) [q.IsPrime]


-- The helper unfolds to separability under the canonical local algebra.
example : Algebra.IsResidueSeparableAt R q ↔
    (letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q;
    Algebra.IsSeparable (q.under R).ResidueField q.ResidueField) :=
  Algebra.isResidueSeparableAt_iff R q

-- Tame ramification: constructor and projections.
example (hsep : Algebra.IsResidueSeparableAt R q)
    (hchar : ¬ ringChar q.ResidueField ∣ q.ramificationIdx R) :
    Algebra.IsTamelyRamifiedAt R q :=
  Algebra.isTamelyRamifiedAt_mk R q hsep hchar

example (htame : Algebra.IsTamelyRamifiedAt R q) :
    Algebra.IsResidueSeparableAt R q ∧
      ¬ ringChar q.ResidueField ∣ q.ramificationIdx R :=
  ⟨htame.isSeparable, htame.not_dvd⟩

-- Wild ramification from characteristic divisibility alone: no separability
-- hypothesis is needed on this branch.
example (hdvd : ringChar q.ResidueField ∣ q.ramificationIdx R) :
    Algebra.IsWildlyRamifiedAt R q :=
  Algebra.isWildlyRamifiedAt_of_char_dvd R q hdvd

-- Wild ramification from residue inseparability: the other complement branch.
example (h : ¬ Algebra.IsResidueSeparableAt R q) :
    Algebra.IsWildlyRamifiedAt R q :=
  Algebra.isWildlyRamifiedAt_of_not_isResidueSeparableAt R q h

example (hsep : Algebra.IsResidueSeparableAt R q)
    (hwild : Algebra.IsWildlyRamifiedAt R q) :
    ringChar q.ResidueField ∣ q.ramificationIdx R :=
  (Algebra.isWildlyRamifiedAt_iff_char_dvd R q hsep).mp hwild

-- Wild ramification is the complement of tame ramification.
example (hwild : Algebra.IsWildlyRamifiedAt R q)
    (htame : Algebra.IsTamelyRamifiedAt R q) : False :=
  (Algebra.isWildlyRamifiedAt_iff R q).mp hwild htame

-- Residue separability at an unramified prime, under the weaker
-- `EssFiniteType` hypothesis.
example [Algebra.EssFiniteType R S] [Algebra.IsUnramifiedAt R q] :
    Algebra.IsResidueSeparableAt R q :=
  Algebra.isResidueSeparableAt_of_isUnramifiedAt R q

-- Unramified primes are tamely ramified, under the weaker `EssFiniteType`
-- hypothesis.
example [Algebra.EssFiniteType R S] [Algebra.IsUnramifiedAt R q] :
    Algebra.IsTamelyRamifiedAt R q :=
  Algebra.isTamelyRamifiedAt_of_isUnramifiedAt R q

-- Characteristic-zero specialization, both directions.
example [Module.Finite R S] (hchar : ringChar q.ResidueField = 0)
    (hsep : Algebra.IsResidueSeparableAt R q) :
    Algebra.IsTamelyRamifiedAt R q :=
  (Algebra.isTamelyRamifiedAt_iff_isSeparable_of_charZero R q hchar).mpr hsep

example [Module.Finite R S] (hchar : ringChar q.ResidueField = 0)
    (htame : Algebra.IsTamelyRamifiedAt R q) :
    Algebra.IsResidueSeparableAt R q :=
  (Algebra.isTamelyRamifiedAt_iff_isSeparable_of_charZero R q hchar).mp htame

-- Characteristic-zero hypothesis discharged from `CharZero`.
example [Module.Finite R S] [CharZero q.ResidueField]
    (hsep : Algebra.IsResidueSeparableAt R q) :
    Algebra.IsTamelyRamifiedAt R q :=
  (Algebra.isTamelyRamifiedAt_iff_isSeparable_of_charZero R q
    ringChar.eq_zero).mpr hsep

