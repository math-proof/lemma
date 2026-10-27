import Mathlib
import Initialize.Tactic.Attr.Basic


namespace IsDedekindDomain

/--
[uniqueFactorizationMonoid_iff_isPrincipalIdealRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindUFDPID.lean)
-/
@[path]
lemma uniqueFactorizationMonoid_iff_isPrincipalIdealRing
  {R : Type*}
  [CommRing R]
  [IsDedekindDomain R] :
-- imply
  UniqueFactorizationMonoid R ↔ IsPrincipalIdealRing R := by
-- proof
  constructor
  · intro
    exact IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid R
  · intro
    exact PrincipalIdealRing.to_uniqueFactorizationMonoid

end IsDedekindDomain

namespace IsDedekindDomain

/--
[isPrincipalIdealRing_iff_subsingleton_classGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindUFDPID.lean)
-/
@[path]
lemma isPrincipalIdealRing_iff_subsingleton_classGroup
  {R : Type*}
  [CommRing R]
  [IsDedekindDomain R] :
-- imply
  IsPrincipalIdealRing R ↔ Subsingleton (ClassGroup R) := by
-- proof
  constructor
  · intro
    have : Fintype.card (ClassGroup R) = 1 := card_classGroup_eq_one
    rw [← Fintype.card_le_one_iff_subsingleton]
    omega
  · intro
    letI : Fintype (ClassGroup R) := Fintype.ofSubsingleton (default : ClassGroup R)
    rw [← card_classGroup_eq_one_iff]
    exact Fintype.card_ofSubsingleton _

end IsDedekindDomain

namespace IsDedekindDomain

/--
[uniqueFactorizationMonoid_iff_subsingleton_classGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindUFDPID.lean)
-/
@[path]
lemma uniqueFactorizationMonoid_iff_subsingleton_classGroup
  {R : Type*}
  [CommRing R]
  [IsDedekindDomain R] :
-- imply
  UniqueFactorizationMonoid R ↔ Subsingleton (ClassGroup R) :=
-- proof
  (uniqueFactorizationMonoid_iff_isPrincipalIdealRing R).trans
    (isPrincipalIdealRing_iff_subsingleton_classGroup R)

end IsDedekindDomain


-- created on 2026-10-23
