import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraNotes.code.IdealFactorization.Part2
open IdealFactorization
open UniqueFactorizationMonoid NumberField


namespace IdealFactorization

/--
[numberField_ideal_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/IdealFactorization.lean)
-/
@[path]
lemma numberField_ideal_factorization
  {K : Type*}
  [Field K]
  [NumberField K]
  {I : Ideal (NumberField.RingOfIntegers K)}
-- given
  (hI : I ≠ ⊥) :
-- imply
  (∀ P ∈ normalizedFactors I, Prime P) ∧ Associated (normalizedFactors I).prod I :=
-- proof
  ⟨fun P hP => prime_of_normalized_factor P hP, prod_normalizedFactors hI⟩

end IdealFactorization

namespace IdealFactorization

/--
[ideal_mul_properties](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/IdealFactorization.lean)
-/
@[path]
lemma ideal_mul_properties
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R] :
-- imply
  (∀ (I I' J : Ideal R), J ≠ ⊥ → I * J = I' * J → I = I') ∧ (∀ (I J : Ideal R), I ≤ J → ∃ J' : Ideal R, I = J * J') := by
-- proof
  constructor
  ·
    intro I I' J hJ h
    have h' : J * I = J * I' := by rw [mul_comm, h, mul_comm]
    exact mul_left_cancel₀ hJ h'
  ·
    intro I J hIJ
    have hdvd : J ∣ I := Ideal.dvd_iff_le.mpr hIJ
    obtain ⟨J', hJ'⟩ := hdvd
    exact ⟨J', hJ'⟩

end IdealFactorization

namespace IdealFactorization

/--
[ideal_is_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/IdealFactorization.lean)
-/
@[path]
lemma ideal_is_lattice
  [CommRing R]
  [IsDomain R]
  [Module.Free ℤ R]
  [Module.Finite ℤ R]
  {I : Ideal R}
-- given
  (hI : I ≠ ⊥) :
-- imply
  Module.Free ℤ I ∧ Module.Finite ℤ I ∧ Module.finrank ℤ I = Module.finrank ℤ R := by
-- proof
  have b := Module.Free.chooseBasis ℤ R
  have hbasis := Submodule.basisOfPid b (I.restrictScalars ℤ)
  refine ⟨Module.Free.of_basis hbasis.2, Module.Finite.of_basis hbasis.2, ?_⟩
  have hfin : Finite (R ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  exact (Submodule.finiteQuotient_iff (I.restrictScalars ℤ)).mp hfin

end IdealFactorization

namespace IdealFactorization

/--
[similar_mul_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/IdealFactorization.lean)
-/
@[path]
lemma similar_mul_right
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {I I' J : Ideal R}
-- given
  (h : IdealsSimilar I I') :
-- imply
  IdealsSimilar (I * J) (I' * J) := by
-- proof
  obtain ⟨a, b, ha, hb, hab⟩ := h
  exact ⟨a, b, ha, hb, by rw [← mul_assoc, ← mul_assoc, hab]⟩

end IdealFactorization


-- created on 2026-10-23
