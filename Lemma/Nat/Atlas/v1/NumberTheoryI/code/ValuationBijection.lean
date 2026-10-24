import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.ValuationBijection
open IsDedekindDomain


/--
[extending_valuation_bijection_primes_above](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ValuationBijection.lean)
-/
@[path]
lemma extending_valuation_bijection_primes_above
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDedekindDomain B]
  {𝔭 : HeightOneSpectrum A} :
-- imply
  (∀ 𝔮₁ 𝔮₂ : HeightOneSpectrum B, 𝔮₁ ∈ primesAbove A B 𝔭 → 𝔮₂ ∈ primesAbove A B 𝔭 → (𝔮₁.valuation L).IsEquiv (𝔮₂.valuation L) → 𝔮₁ = 𝔮₂) ∧ (∀ w : Valuation L (WithZero (Multiplicative ℤ)), ExtendsValuation A K L 𝔭 w → ∃ 𝔮 : HeightOneSpectrum B, 𝔮 ∈ primesAbove A B 𝔭 ∧ (𝔮.valuation L).IsEquiv w) := by
-- proof
  constructor
  ·
    intro 𝔮₁ 𝔮₂ _ _ hEquiv
    have hlt : ∀ x : L, (𝔮₁.valuation L) x < 1 ↔ (𝔮₂.valuation L) x < 1 :=
      fun x => (Valuation.isEquiv_iff_val_lt_one.mp hEquiv)
    have hIdeal : 𝔮₁.asIdeal = 𝔮₂.asIdeal := by
      ext r
      rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) 𝔮₁,
        ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) 𝔮₂]
      exact hlt (algebraMap B L r)
    exact HeightOneSpectrum.ext hIdeal
  ·
    exact valuation_surjective_of_extends A K L B 𝔭

/--
[mem_of_liesOver](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ValuationBijection.lean)
-/
@[path]
private lemma mem_of_liesOver_eq
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDedekindDomain B]
  {𝔭 : HeightOneSpectrum A}
  {𝔮 : HeightOneSpectrum B}
  {a : A}
-- given
  (hlo : 𝔮.asIdeal.LiesOver 𝔭.asIdeal) :
-- imply
  a ∈ 𝔭.asIdeal ↔ algebraMap A B a ∈ 𝔮.asIdeal := by
-- proof
  apply mem_of_liesOver A K L B 𝔭 𝔮 hlo a

/--
[valuation_extends_of_liesOver](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ValuationBijection.lean)
-/
@[path]
private lemma valuation_extends_of_liesOver_eq
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDedekindDomain B]
  {𝔭 : HeightOneSpectrum A}
  {𝔮 : HeightOneSpectrum B}
-- given
  (hlo : 𝔮.asIdeal.LiesOver 𝔭.asIdeal) :
-- imply
  ExtendsValuation A K L 𝔭 (𝔮.valuation L) := by
-- proof
  apply valuation_extends_of_liesOver A K L B 𝔭 𝔮 hlo

/--
[dvr_overring_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ValuationBijection.lean)
-/
@[path]
private lemma dvr_overring_equiv_eq
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDedekindDomain B]
  [CommRing B']
  [IsDomain B']
  [IsDedekindDomain B']
  [Field L']
  [Algebra B' L']
  [IsFractionRing B' L']
  {𝔮 : HeightOneSpectrum B'}
  {w : Valuation L' (WithZero (Multiplicative ℤ))}
-- given
  (hB : ∀ b : B', w (algebraMap B' L' b) ≤ 1)
  (hIdeal : ∀ b : B', b ∈ 𝔮.asIdeal ↔ w (algebraMap B' L' b) < 1) :
-- imply
  (𝔮.valuation L').IsEquiv w := by
-- proof
  apply dvr_overring_equiv A K L B 𝔮 w hB hIdeal

/--
[valuation_surjective_of_extends](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ValuationBijection.lean)
-/
@[path]
private lemma valuation_surjective_of_extends_eq
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDedekindDomain B]
  {𝔭 : HeightOneSpectrum A}
  {w : Valuation L (WithZero (Multiplicative ℤ))}
-- given
  (hw : ExtendsValuation A K L 𝔭 w) :
-- imply
  ∃ 𝔮 : HeightOneSpectrum B, 𝔮 ∈ primesAbove A B 𝔭 ∧ (𝔮.valuation L).IsEquiv w := by
-- proof
  apply valuation_surjective_of_extends A K L B 𝔭 w hw


-- created on 2026-10-23
