import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.NumberField.PlaceTransport
open scoped NumberField.PlaceTransport
open scoped Pointwise
open IsDedekindDomain NumberField


/-- ported from external source -/

private lemma  numberField_of_algebra (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K] : NumberField E := by
  have : CharZero E := RingHom.charZero (algebraMap E K)
  exact { to_charZero := inferInstance,
          to_finiteDimensional :=
            FiniteDimensional.of_injective (algebraMap E K).toRatAlgHom.toLinearMap (algebraMap E K).injective }

private lemma  smul_asIdeal_eq (E K : Type*) [Field E] [Field K] [Algebra E K] (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) :
  (σ • w).asIdeal = σ • w.asIdeal := by
  ext x
  rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem]


open in
@[path]
private lemma main
  [Field E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
  {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} :
-- imply
  MulAction.orbit (K ≃ₐ[E] K) w =
      {w' | w'.under (NumberField.RingOfIntegers E) = w.under (NumberField.RingOfIntegers E)} := by
-- proof
  classical
    have : NumberField E := numberField_of_algebra E K
    have : w.asIdeal.IsPrime := w.isPrime
    have : w.asIdeal.LiesOver (w.under (𝓞 E)).asIdeal := ⟨rfl⟩
    have horb := Algebra.IsInvariant.orbit_eq_primesOver (𝓞 E) (𝓞 K) (K ≃ₐ[E] K) (w.under (𝓞 E)).asIdeal w.asIdeal
    ext w'
    constructor
    ·
      rintro ⟨σ, rfl⟩
      apply HeightOneSpectrum.ext
      change Ideal.under (𝓞 E) (σ • w).asIdeal = Ideal.under (𝓞 E) w.asIdeal
      rw [smul_asIdeal_eq, Ideal.under_smul]
    ·
      intro hw'
      have hmem : w'.asIdeal ∈ (w.under (𝓞 E)).asIdeal.primesOver (𝓞 K) :=
        ⟨w'.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw').symm⟩⟩
      rw [← horb] at hmem
      obtain ⟨σ, hσ⟩ := hmem
      refine ⟨σ, HeightOneSpectrum.ext ?_⟩
      change (σ • w).asIdeal = w'.asIdeal
      rwa [smul_asIdeal_eq]


-- created on 2026-10-23
