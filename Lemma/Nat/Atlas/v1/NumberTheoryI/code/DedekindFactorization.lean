import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.DedekindFactorization
open IsDedekindDomain
open scoped nonZeroDivisors


/--
[FractionalIdeal.unique_factorization_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindFactorization.lean)
-/
@[path]
lemma FractionalIdeal.unique_factorization_exists
  [CommRing R]
  [IsDedekindDomain R]
  {I : FractionalIdeal R⁰ K}
-- given
  (hI : I ≠ 0) :
-- imply
  ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ (FractionalIdeal.count K v I) = I :=
-- proof
  FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI

/--
[FractionalIdeal.unique_factorization_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindFactorization.lean)
-/
@[path]
lemma FractionalIdeal.unique_factorization_unique
  [CommRing R]
  [IsDedekindDomain R]
  {I : FractionalIdeal R⁰ K}
  {e : HeightOneSpectrum R → ℤ}
  {v : HeightOneSpectrum R}
-- given
  (_hI : I ≠ 0)
  (he : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, e v = 0)
  (hprod : ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ e v = I) :
-- imply
  e v = FractionalIdeal.count K v I := by
-- proof
  have h1 : FractionalIdeal.count K v
    (∏ᶠ w : HeightOneSpectrum R, (w.asIdeal : FractionalIdeal R⁰ K) ^ e w) = e v :=
    FractionalIdeal.count_finprod K v e he
  rwa [hprod] at h1

/--
[FractionalIdeal.unique_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindFactorization.lean)
-/
@[path]
lemma FractionalIdeal.unique_factorization
  [CommRing R]
  [IsDedekindDomain R]
  {I : FractionalIdeal R⁰ K}
-- given
  (hI : I ≠ 0) :
-- imply
  (∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ (FractionalIdeal.count K v I) = I) ∧ (∀ (e : HeightOneSpectrum R → ℤ), (∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, e v = 0) → (∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ e v = I) → ∀ v : HeightOneSpectrum R, e v = FractionalIdeal.count K v I) :=
-- proof
  ⟨FractionalIdeal.unique_factorization_exists K hI,
    fun e he hprod v => FractionalIdeal.unique_factorization_unique K hI e he hprod v⟩


-- created on 2026-10-23
