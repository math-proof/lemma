import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.NumberTheoryI.code.Chapter1.IntegralClosure


/--
[isIntegral_add_and_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/IntegralClosure.lean)
-/
@[path]
lemma isIntegral_add_and_mul
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  {α β : B}
-- given
  (hα : IsIntegral A α)
  (hβ : IsIntegral A β) :
-- imply
  IsIntegral A (α + β) ∧ IsIntegral A (α * β) :=
-- proof
  ⟨hα.add hβ, hα.mul hβ⟩

/--
[proposition_1_20](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/IntegralClosure.lean)
-/
@[path]
lemma proposition_1_20
  [CommRing A]
  [CommRing B]
  [CommRing C]
  [Algebra A B]
  [Algebra B C]
  [Algebra A C]
  [IsScalarTower A B C]
-- given
  (hAB : Algebra.IsIntegral A B)
  (hBC : Algebra.IsIntegral B C) :
-- imply
  Algebra.IsIntegral A C :=
-- proof
Algebra.IsIntegral.trans B

/--
[corollary_1_21'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/IntegralClosure.lean)
-/
@[path]
lemma corollary_1_21'
  {A B : Type*}
  [CommRing A]
  [CommRing B]
  [Algebra A B] :
-- imply
  IsIntegrallyClosedIn (integralClosure A B) B :=
-- proof
  inferInstance

/--
[proposition_1_22](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/IntegralClosure.lean)
-/
@[path]
lemma proposition_1_22
-- imply
  IsIntegrallyClosed ℤ :=
-- proof
  inferInstance

/--
[corollary_1_23](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/IntegralClosure.lean)
-/
@[path]
lemma corollary_1_23
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [UniqueFactorizationMonoid A] :
-- imply
  IsIntegrallyClosed A :=
-- proof
  inferInstance

/--
[proposition_1_25](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/IntegralClosure.lean)
-/
@[path]
lemma proposition_1_25
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [ValuationRing A] :
-- imply
  IsIntegrallyClosed A :=
-- proof
  inferInstance

/--
[proposition_1_28](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/IntegralClosure.lean)
-/
@[path]
lemma proposition_1_28
  [CommRing A]
  [IsDomain A]
  [IsIntegrallyClosed A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [Field L]
  [Algebra K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {α : L}
-- given
  (hα : IsAlgebraic K α) :
-- imply
  IsIntegral A α ↔ ∀ i, (minpoly K α).coeff i ∈ (algebraMap A K).range := by
-- proof
  constructor
  ·
    intro hInt
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hInt]
    intro i
    rw [Polynomial.coeff_map]
    exact ⟨_, rfl⟩
  ·
    intro hcoeff
    have hlift : minpoly K α ∈ Polynomial.lifts (algebraMap A K) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr hcoeff
    have hmonic : (minpoly K α).Monic := minpoly.monic hα.isIntegral
    obtain ⟨q, hq_map, _, hq_monic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hmonic
    have hq_root : Polynomial.aeval α q = 0 := by
      have h : Polynomial.aeval α (q.map (algebraMap A K)) = 0 := by
        rw [hq_map]; exact minpoly.aeval K α
      rwa [Polynomial.aeval_map_algebraMap (R := A) (A := K)] at h
    exact ⟨q, hq_monic, hq_root⟩


-- created on 2026-10-23
