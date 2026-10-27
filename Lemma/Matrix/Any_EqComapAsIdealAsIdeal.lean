import Initialize.Tactic.Attr.Basic
import Mathlib
open IsDedekindDomain NumberField


@[path]
private lemma main
  [Field E] [NumberField E]
  [Field K] [Algebra E K]
-- given
  (v : HeightOneSpectrum (𝓞 E)) :
-- imply
  ∃ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
-- proof
  have hinj : Function.Injective (algebraMap (𝓞 E) (𝓞 K)) := fun x y hxy => by
    apply IsIntegralClosure.algebraMap_injective (𝓞 E) ℤ E
    apply (algebraMap E K).injective
    have := congrArg (algebraMap (𝓞 K) K) hxy
    rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 E) E K, IsScalarTower.algebraMap_apply (𝓞 E) E K] at this
  have := v.isMaximal
  have hker : RingHom.ker (algebraMap (𝓞 E) (𝓞 K)) ≤ v.asIdeal := by
    simp [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
  obtain ⟨W, hWmax, hWv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) v.asIdeal hker
  refine ⟨⟨W, hWmax.isPrime, ?_⟩, ?_⟩
  ·
    rintro rfl
    exact v.ne_bot (hWv.symm.trans (Ideal.comap_bot_of_injective _ hinj))
  ·
    simpa [Ideal.under] using hWv


-- created on 2026-10-24
