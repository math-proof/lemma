import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RamificationInertia.Tame
open Algebra


namespace Algebra

/--
[isResidueSeparableAt_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
lemma isResidueSeparableAt_iff
  [CommRing R] [CommRing S] [Algebra R S]
  {q : Ideal S} [q.IsPrime] :
-- imply
  IsResidueSeparableAt R q ↔
    letI :=
-- proof
  Iff.rfl

end Algebra

namespace Algebra

/--
[isTamelyRamifiedAt_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
lemma isTamelyRamifiedAt_iff
  [CommRing R] [CommRing S] [Algebra R S]
  {q : Ideal S} [q.IsPrime] :
-- imply
  IsTamelyRamifiedAt R q ↔
    IsResidueSeparableAt R q ∧
    ¬ ringChar q.ResidueField ∣ q.ramificationIdx R :=
-- proof
  Iff.rfl

end Algebra

namespace Algebra

/--
[isWildlyRamifiedAt_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
lemma isWildlyRamifiedAt_iff
  [CommRing R] [CommRing S] [Algebra R S]
  {q : Ideal S} [q.IsPrime] :
-- imply
  IsWildlyRamifiedAt R q ↔ ¬ IsTamelyRamifiedAt R q :=
-- proof
  Iff.rfl

end Algebra

namespace Algebra

/--
[isTamelyRamifiedAt_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
lemma isTamelyRamifiedAt_mk
  [CommRing R] [CommRing S] [Algebra R S]
  {q : Ideal S} [q.IsPrime]
-- given
  (hsep : IsResidueSeparableAt R q)
  (hchar : ¬ ringChar q.ResidueField ∣ q.ramificationIdx R) :
-- imply
  IsTamelyRamifiedAt R q :=
-- proof
  ⟨hsep, hchar⟩

end Algebra

namespace Algebra

/--
[IsTamelyRamifiedAt.isSeparable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
lemma IsTamelyRamifiedAt.isSeparable
  [CommRing R] [CommRing S] [Algebra R S]
  {q : Ideal S} [q.IsPrime]
-- given
  (h : IsTamelyRamifiedAt R q) :
-- imply
  IsResidueSeparableAt R q :=
-- proof
  h.1

end Algebra

namespace Algebra

/--
[IsTamelyRamifiedAt.not_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
lemma IsTamelyRamifiedAt.not_dvd
  [CommRing R] [CommRing S] [Algebra R S]
  {q : Ideal S} [q.IsPrime]
-- given
  (h : IsTamelyRamifiedAt R q) :
-- imply
  ¬ ringChar q.ResidueField ∣ q.ramificationIdx R :=
-- proof
  h.2

end Algebra

namespace Algebra

/--
[isWildlyRamifiedAt_iff_char_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
lemma isWildlyRamifiedAt_iff_char_dvd
  [CommRing R] [CommRing S] [Algebra R S]
  {q : Ideal S} [q.IsPrime]
-- given
  (hsep : IsResidueSeparableAt R q) :
-- imply
  IsWildlyRamifiedAt R q ↔ ringChar q.ResidueField ∣ q.ramificationIdx R := by
-- proof
  constructor
  · intro hwild
    by_contra hdvd
    exact hwild ⟨hsep, hdvd⟩
  · intro hdvd htame
    exact htame.2 hdvd

end Algebra

namespace Algebra

/--
[isWildlyRamifiedAt_of_char_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
lemma isWildlyRamifiedAt_of_char_dvd
  [CommRing R] [CommRing S] [Algebra R S]
  {q : Ideal S} [q.IsPrime]
-- given
  (hdvd : ringChar q.ResidueField ∣ q.ramificationIdx R) :
-- imply
  IsWildlyRamifiedAt R q :=
-- proof
  fun htame => htame.2 hdvd

end Algebra

namespace Algebra

/--
[isWildlyRamifiedAt_of_not_isResidueSeparableAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
lemma isWildlyRamifiedAt_of_not_isResidueSeparableAt
  [CommRing R] [CommRing S] [Algebra R S]
  {q : Ideal S} [q.IsPrime]
-- given
  (h : ¬ IsResidueSeparableAt R q) :
-- imply
  IsWildlyRamifiedAt R q :=
-- proof
  fun htame => h htame.1

end Algebra

namespace Algebra

/--
[isResidueSeparableAt_of_isUnramifiedAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
lemma isResidueSeparableAt_of_isUnramifiedAt
  [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
  {q : Ideal S} [q.IsPrime] [Algebra.IsUnramifiedAt R q] :
-- imply
  IsResidueSeparableAt R q := by
-- proof
  let := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  have h : Algebra.IsSeparable (q.under R).ResidueField q.ResidueField :=
    inferInstance
  exact h

end Algebra

namespace Algebra

/--
[isTamelyRamifiedAt_of_isUnramifiedAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
lemma isTamelyRamifiedAt_of_isUnramifiedAt
  [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
  {q : Ideal S} [q.IsPrime] [Algebra.IsUnramifiedAt R q] :
-- imply
  IsTamelyRamifiedAt R q := by
-- proof
  refine ⟨isResidueSeparableAt_of_isUnramifiedAt R q, ?_⟩
  rw [Ideal.ramificationIdx_eq_one q R]
  exact fun h => CharP.ringChar_ne_one (Nat.eq_one_of_dvd_one h)

end Algebra

namespace Algebra

/--
[isTamelyRamifiedAt_iff_isSeparable_of_charZero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Tame.lean)
-/
@[path]
lemma isTamelyRamifiedAt_iff_isSeparable_of_charZero
  [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
  {q : Ideal S} [q.IsPrime]
-- given
  (hchar : ringChar q.ResidueField = 0) :
-- imply
  IsTamelyRamifiedAt R q ↔ IsResidueSeparableAt R q := by
-- proof
  rw [isTamelyRamifiedAt_iff R q, hchar]
  refine and_iff_left (fun hdvd => ?_)
  exact (Ideal.ramificationIdx_pos q R).ne' (Nat.zero_dvd.mp hdvd)

end Algebra


-- created on 2026-10-20
-- updated on 2026-10-23
