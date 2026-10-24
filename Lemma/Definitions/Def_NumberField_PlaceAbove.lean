import Mathlib

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace NumberField.PlaceAbove

variable (E K : Type*) [Field E] [NumberField E] [Field K] [Algebra E K]

theorem exists_above (v : HeightOneSpectrum (𝓞 E)) :
    ∃ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
  have hinj : Function.Injective (algebraMap (𝓞 E) (𝓞 K)) := fun x y hxy => by
    apply IsIntegralClosure.algebraMap_injective (𝓞 E) ℤ E
    apply (algebraMap E K).injective
    have := congrArg (algebraMap (𝓞 K) K) hxy
    rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 E) E K, IsScalarTower.algebraMap_apply (𝓞 E) E K] at this
  haveI := v.isMaximal
  obtain ⟨W, hWmax, hWv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) v.asIdeal
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  have hW0 : W ≠ ⊥ := by
    rintro rfl
    exact v.ne_bot (by rw [← hWv, Ideal.comap_bot_of_injective _ hinj])
  exact ⟨⟨W, hWmax.isPrime, hW0⟩, hWv⟩

noncomputable def above (v : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 K) := (exists_above E K v).choose

theorem comap_above (v : HeightOneSpectrum (𝓞 E)) :
    (above E K v).asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := (exists_above E K v).choose_spec

end NumberField.PlaceAbove
