import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RamificationInertia.Tame
open Algebra


/--
[isResidueSeparableAt_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
private lemma isResidueSeparableAt_iff_eq
  [CommRing R] [CommRing S] [Algebra R S]
  {q : Ideal S} [q.IsPrime] :
-- imply
  IsResidueSeparableAt R q ↔
    letI := by
-- proof
  apply Algebra.isResidueSeparableAt_iff R q

/--
[isTamelyRamifiedAt_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
private lemma isTamelyRamifiedAt_iff_eq
  [CommRing R] [CommRing S] [Algebra R S]
  {q : Ideal S} [q.IsPrime] :
-- imply
  IsTamelyRamifiedAt R q ↔
    IsResidueSeparableAt R q ∧
    ¬ ringChar q.ResidueField ∣ q.ramificationIdx R := by
-- proof
  apply Algebra.isTamelyRamifiedAt_iff R q

/--
[isWildlyRamifiedAt_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
private lemma isWildlyRamifiedAt_iff_eq
  [CommRing R] [CommRing S] [Algebra R S]
  {q : Ideal S} [q.IsPrime] :
-- imply
  IsWildlyRamifiedAt R q ↔ ¬ IsTamelyRamifiedAt R q := by
-- proof
  apply Algebra.isWildlyRamifiedAt_iff R q

/--
[isTamelyRamifiedAt_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
private lemma isTamelyRamifiedAt_mk_eq
  [CommRing R] [CommRing S] [Algebra R S]
  {q : Ideal S} [q.IsPrime]
-- given
  (hsep : IsResidueSeparableAt R q)
  (hchar : ¬ ringChar q.ResidueField ∣ q.ramificationIdx R) :
-- imply
  IsTamelyRamifiedAt R q := by
-- proof
  apply Algebra.isTamelyRamifiedAt_mk R q hsep hchar

/--
[IsTamelyRamifiedAt.isSeparable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
private lemma IsTamelyRamifiedAt_isSeparable_eq
  [CommRing R] [CommRing S] [Algebra R S]
  {q : Ideal S} [q.IsPrime]
-- given
  (h : IsTamelyRamifiedAt R q) :
-- imply
  IsResidueSeparableAt R q := by
-- proof
  apply Algebra.IsTamelyRamifiedAt.isSeparable R q h

/--
[IsTamelyRamifiedAt.not_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
private lemma IsTamelyRamifiedAt_not_dvd_eq
  [CommRing R] [CommRing S] [Algebra R S]
  {q : Ideal S} [q.IsPrime]
-- given
  (h : IsTamelyRamifiedAt R q) :
-- imply
  ¬ ringChar q.ResidueField ∣ q.ramificationIdx R := by
-- proof
  apply Algebra.IsTamelyRamifiedAt.not_dvd R q h

/--
[isWildlyRamifiedAt_iff_char_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
private lemma isWildlyRamifiedAt_iff_char_dvd_eq
  [CommRing R] [CommRing S] [Algebra R S]
  {q : Ideal S} [q.IsPrime]
-- given
  (hsep : IsResidueSeparableAt R q) :
-- imply
  IsWildlyRamifiedAt R q ↔ ringChar q.ResidueField ∣ q.ramificationIdx R := by
-- proof
  apply Algebra.isWildlyRamifiedAt_iff_char_dvd R q hsep

/--
[isWildlyRamifiedAt_of_char_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
private lemma isWildlyRamifiedAt_of_char_dvd_eq
  [CommRing R] [CommRing S] [Algebra R S]
  {q : Ideal S} [q.IsPrime]
-- given
  (hdvd : ringChar q.ResidueField ∣ q.ramificationIdx R) :
-- imply
  IsWildlyRamifiedAt R q := by
-- proof
  apply Algebra.isWildlyRamifiedAt_of_char_dvd R q hdvd

/--
[isWildlyRamifiedAt_of_not_isResidueSeparableAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
private lemma isWildlyRamifiedAt_of_not_isResidueSeparableAt_eq
  [CommRing R] [CommRing S] [Algebra R S]
  {q : Ideal S} [q.IsPrime]
-- given
  (h : ¬ IsResidueSeparableAt R q) :
-- imply
  IsWildlyRamifiedAt R q := by
-- proof
  apply Algebra.isWildlyRamifiedAt_of_not_isResidueSeparableAt R q h

/--
[isResidueSeparableAt_of_isUnramifiedAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
private lemma isResidueSeparableAt_of_isUnramifiedAt_eq
  [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
  {q : Ideal S} [q.IsPrime] [Algebra.IsUnramifiedAt R q] :
-- imply
  IsResidueSeparableAt R q := by
-- proof
  apply Algebra.isResidueSeparableAt_of_isUnramifiedAt R q

/--
[isTamelyRamifiedAt_of_isUnramifiedAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
private lemma isTamelyRamifiedAt_of_isUnramifiedAt_eq
  [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
  {q : Ideal S} [q.IsPrime] [Algebra.IsUnramifiedAt R q] :
-- imply
  IsTamelyRamifiedAt R q := by
-- proof
  apply Algebra.isTamelyRamifiedAt_of_isUnramifiedAt R q

/--
[isTamelyRamifiedAt_iff_isSeparable_of_charZero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
private lemma isTamelyRamifiedAt_iff_isSeparable_of_charZero_eq
  [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
  {q : Ideal S} [q.IsPrime]
-- given
  (hchar : ringChar q.ResidueField = 0) :
-- imply
  IsTamelyRamifiedAt R q ↔ IsResidueSeparableAt R q := by
-- proof
  apply Algebra.isTamelyRamifiedAt_iff_isSeparable_of_charZero R q hchar


-- created on 2026-10-20
