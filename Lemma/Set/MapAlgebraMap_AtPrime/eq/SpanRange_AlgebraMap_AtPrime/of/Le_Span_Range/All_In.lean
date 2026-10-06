import Mathlib
import sympy.Basic


/--
[Ideal_map_algebraMap_localizationAtPrime_eq_span_of_le_span_sup_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_map_algebraMap_localizationAtPrime_eq_span_of_le_span_sup_mul.lean)
-/
@[main]
private lemma main
  {P : Type u} [CommRing P] [IsNoetherianRing P]
  {J : Ideal P}
  {𝔫 : Ideal P} [𝔫.IsPrime]
  {ι : Type v}
-- given
  (h : ι → P)
  (hh : ∀ i, h i ∈ J)
  (hle : J ≤ Ideal.span (Set.range h) ⊔ 𝔫 * J) :
-- imply
  Ideal.map (algebraMap P (Localization.AtPrime 𝔫)) J =
      Ideal.span (Set.range fun i => algebraMap P (Localization.AtPrime 𝔫) (h i)) := by
-- proof
  classical
  set S := Localization.AtPrime 𝔫 with hS
  set M : Ideal S := J.map (algebraMap P S) with hM
  set N : Ideal S := Ideal.span (Set.range fun i => algebraMap P S (h i)) with hN
  have hNeq : N = (Ideal.span (Set.range h)).map (algebraMap P S) := by
    rw [Ideal.map_span, ← Set.range_comp]; rfl
  have hNM : N ≤ M := by
    rw [hNeq]
    exact Ideal.map_mono (Ideal.span_le.2 (Set.range_subset_iff.2 hh))
  refine le_antisymm ?_ hNM

  have hMfg : M.FG := IsNoetherian.noetherian M
  refine Submodule.le_of_le_smul_of_le_jacobson_bot hMfg (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_

  have h1 : M ≤ (Ideal.span (Set.range h) ⊔ 𝔫 * J).map (algebraMap P S) := Ideal.map_mono hle
  refine h1.trans ?_
  rw [Ideal.map_sup, Ideal.map_mul, ← hNeq]
  refine sup_le le_sup_left (le_sup_right.trans' ?_)
  rw [Ideal.smul_eq_mul]
  refine Ideal.mul_mono_left ?_
  exact (Localization.AtPrime.map_eq_maximalIdeal (I := 𝔫)).le


-- created on 2026-10-05
