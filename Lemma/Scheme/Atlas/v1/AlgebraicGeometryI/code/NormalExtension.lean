import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.NormalExtension
open AlgebraicHartogs


namespace AlgebraicHartogs

/--
[HeightOnePrime.ne_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NormalExtension.lean)
-/
@[path]
lemma HeightOnePrime.ne_bot
  [CommRing A]
  [IsDomain A]
  {p : HeightOnePrime A} :
-- imply
  p.asIdeal ≠ ⊥ := by
-- proof
  intro h
  have h0 : (⊥ : Ideal A).height = 0 := by
    rw [Ideal.height_eq_primeHeight (I := (⊥ : Ideal A)),
      Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]; rfl
  have habs := p.height_eq; rw [h] at habs; simp [h0] at habs

end AlgebraicHartogs

namespace AlgebraicHartogs

/--
[exists_height_one_prime_containing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NormalExtension.lean)
-/
@[path]
lemma exists_height_one_prime_containing
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  {a : A}
-- given
  (ha_ne : a ≠ 0)
  (ha_nu : ¬IsUnit a) :
-- imply
  ∃ p : HeightOnePrime A, a ∈ p.asIdeal := by
-- proof
  have hne_top : Ideal.span ({a} : Set A) ≠ ⊤ := by rwa [Ne, Ideal.span_singleton_eq_top]
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne_top
  haveI : m.IsPrime := hm.isPrime
  obtain ⟨q, hq_min, _⟩ := Ideal.exists_minimalPrimes_le (J := m) hle
  have hq_prime := Ideal.minimalPrimes_isPrime hq_min
  have ha_q : a ∈ q := hq_min.1.2 (Ideal.mem_span_singleton_self a)
  have hq_le : q.height ≤ 1 := by
    have : Submodule.IsPrincipal (Ideal.span ({a} : Set A)) := ⟨⟨a, by simp⟩⟩
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq_min
  have hq_ge : 1 ≤ q.height := by
    rw [ENat.one_le_iff_ne_zero, Ideal.height_eq_primeHeight]
    intro h0
    rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot] at h0
    exact ha_ne (Ideal.mem_bot.mp ((Set.mem_singleton_iff.mp h0) ▸ ha_q))
  exact ⟨⟨q, hq_prime, le_antisymm hq_le hq_ge⟩, ha_q⟩

end AlgebraicHartogs

namespace AlgebraicHartogs

/--
[mem_of_mem_all_prime_localizations](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NormalExtension.lean)
-/
@[path]
lemma mem_of_mem_all_prime_localizations
  [CommRing A]
  [IsDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {x : K}
-- given
  (hx : ∀ v : PrimeSpectrum A, x ∈ Localization.subalgebra.ofField K v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors) :
-- imply
  x ∈ Set.range (algebraMap A K) :=
-- proof
  Algebra.mem_bot.mp ((PrimeSpectrum.iInf_localization_eq_bot A K) ▸ (Algebra.mem_iInf.mpr hx))

end AlgebraicHartogs

/--
[height_eq_one_of_prime_ne_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NormalExtension.lean)
-/
@[path]
private lemma height_eq_one_of_prime_ne_bot_eq
  [CommRing A]
  [IsDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsDedekindDomain A]
  {p : Ideal A}
  [hp : p.IsPrime]
-- given
  (hne : p ≠ ⊥) :
-- imply
  p.height = 1 := by
-- proof
  apply AlgebraicHartogs.height_eq_one_of_prime_ne_bot p hne

/--
[algebraicHartogs_dedekind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NormalExtension.lean)
-/
@[path]
private lemma algebraicHartogs_dedekind_eq
  [CommRing A]
  [IsDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsDedekindDomain A]
  {x : K}
-- given
  (hx : ∀ v : IsDedekindDomain.HeightOneSpectrum A, x ∈ Localization.subalgebra.ofField K v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors) :
-- imply
  x ∈ Set.range (algebraMap A K) := by
-- proof
  apply AlgebraicHartogs.algebraicHartogs_dedekind x hx


-- created on 2026-10-23
