import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Lemma.Definitions.Def_M4aHerbrand_IdeleClassVocab
import Lemma.Definitions.Def_NumberField_PlaceTransport
import Lemma.Int.P2MUtil

open IsDedekindDomain NumberField
open scoped NumberField.PlaceTransport

/--
[NumberField_AdeleRing_finite_setOf_valued_snd_ne_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_NumberField_AdeleRing_finite_setOf_valued_snd_ne_one.lean)
-/
@[path]
private lemma main
  [Field K] [NumberField K]
  {x : (AdeleRing (𝓞 K) K)ˣ} :
-- imply
  {w : HeightOneSpectrum (𝓞 K) | Valued.v (((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) ≠ 1}.Finite := by
-- proof
  have h1 : ∀ᶠ w in Filter.cofinite, ((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w ∈ (w.adicCompletionIntegers K : Set (w.adicCompletion K)) :=
    ((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K).2
  have h2 : ∀ᶠ w in Filter.cofinite, (((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w ∈ (w.adicCompletionIntegers K : Set (w.adicCompletion K)) :=
    (((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K).2
  have h12 := h1.and h2
  rw [Filter.eventually_cofinite] at h12
  refine h12.subset fun w hw => ?_
  simp only [Set.mem_setOf_eq, not_and_or] at hw ⊢

  by_contra h
  push Not at h
  obtain ⟨hx, hxi⟩ := h
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hx hxi
  have hmul : ((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w * (((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w = 1 := by
    have h : ((((x * x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = 1 := by rw [mul_inv_cancel]; rfl
    exact h
  have hv : Valued.v (((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) * Valued.v ((((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = 1 := by
    rw [← map_mul, hmul, map_one]
  apply hw
  apply le_antisymm hx

  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) * Valued.v ((((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) := hv.symm
    _ ≤ Valued.v (((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) * 1 := mul_le_mul_right hxi _
    _ = _ := mul_one _


-- created on 2026-10-23
