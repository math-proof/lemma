import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.RamificationClosedProp7
open PrimeSpectrum Proposition7


namespace Proposition7

/--
[ramificationLocus_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RamificationClosedProp7.lean)
-/
@[path]
lemma ramificationLocus_isClosed
  {A B : Type*}
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.Free A B] :
-- imply
  IsClosed (ramificationLocus A B) :=
-- proof
  PrimeSpectrum.isClosed_zeroLocus _

end Proposition7

namespace Proposition7

/--
[ramificationLocus_ne_univ_of_discr_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RamificationClosedProp7.lean)
-/
@[path]
lemma ramificationLocus_ne_univ_of_discr_ne_zero
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [CommRing B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.Free A B]
-- given
  (hd : Algebra.discr A (Module.Free.chooseBasis A B) ≠ 0) :
-- imply
  ramificationLocus A B ≠ Set.univ := by
-- proof
  intro h
  have hmem := (PrimeSpectrum.zeroLocus_eq_univ_iff _).mp h
  simp only [Set.singleton_subset_iff, SetLike.mem_coe] at hmem
  rw [nilradical_eq_zero] at hmem
  exact hd hmem

end Proposition7

namespace Proposition7

/--
[discr_ne_zero_of_separable_functionField](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RamificationClosedProp7.lean)
-/
@[path]
lemma discr_ne_zero_of_separable_functionField
  {A : Type*}
  {K : Type*}
  {B : Type*}
  {L : Type*}
  [CommRing A]
  [IsDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [CommRing B]
  [IsDomain B]
  [Field L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A B]
  [Module.Finite A B]
  [Module.Free A B]
  [Algebra K L]
  [Algebra A L]
  [IsScalarTower A K L]
  [IsScalarTower A B L]
  [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L]
  [Algebra.IsSeparable K L]
  [Module.Finite K L] :
-- imply
  Algebra.discr A (Module.Free.chooseBasis A B) ≠ 0 := by
-- proof
  set b := Module.Free.chooseBasis A B
  set b' := b.localizationLocalization K (nonZeroDivisors A) L
  have hlocal : Algebra.discr K b' = (algebraMap A K) (Algebra.discr A b) :=
    Algebra.discr_localizationLocalization A (nonZeroDivisors A) L b
  have hne : Algebra.discr K b' ≠ 0 := Algebra.discr_not_zero_of_basis K b'
  rw [hlocal] at hne
  exact fun h => hne (by rw [h, map_zero])

end Proposition7

namespace Proposition7

/--
[ramificationLocus_ne_univ_of_separable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RamificationClosedProp7.lean)
-/
@[path]
lemma ramificationLocus_ne_univ_of_separable
  {A : Type*}
  {K : Type*}
  {B : Type*}
  {L : Type*}
  [CommRing A]
  [IsDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [CommRing B]
  [IsDomain B]
  [Field L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A B]
  [Module.Finite A B]
  [Module.Free A B]
  [Algebra K L]
  [Algebra A L]
  [IsScalarTower A K L]
  [IsScalarTower A B L]
  [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L]
  [Algebra.IsSeparable K L]
  [Module.Finite K L] :
-- imply
  ramificationLocus A B ≠ Set.univ :=
-- proof
  ramificationLocus_ne_univ_of_discr_ne_zero A B
    (discr_ne_zero_of_separable_functionField A K B L)

end Proposition7


-- created on 2026-10-23
