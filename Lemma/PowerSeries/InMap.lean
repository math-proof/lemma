import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma map_injective [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K] [Algebra R K] [IsFractionRing R K] : Function.Injective (PowerSeries.map (algebraMap R K)) := by
  intro a b h
  ext n
  apply IsFractionRing.injective R K
  have := congrArg (PowerSeries.coeff n) h
  simpa only [PowerSeries.coeff_map] using this
private lemma helper_main [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K] [Algebra R K] [IsFractionRing R K] (g : PowerSeries K) (Φ : Polynomial (PowerSeries R)) (hΦ : Φ.Monic) (hroot : Polynomial.eval₂ (PowerSeries.map (algebraMap R K)) g Φ = 0) (h : PowerSeries R) (h0 : h ≠ 0) (hmul : PowerSeries.map (algebraMap R K) h * g ∈ (PowerSeries.map (algebraMap R K)).range) : g ∈ (PowerSeries.map (algebraMap R K)).range := by
  classical
  set ι : PowerSeries R →+* PowerSeries K := PowerSeries.map (algebraMap R K) with hι
  let F := FractionRing (PowerSeries R)
  let F' := FractionRing (PowerSeries K)
  let alg' : PowerSeries K →+* F' := algebraMap (PowerSeries K) F'
  have hι_inj : Function.Injective ι := map_injective
  have halg'_inj : Function.Injective alg' := IsFractionRing.injective (PowerSeries K) F'
  have hcomp_inj : Function.Injective (alg'.comp ι) := halg'_inj.comp hι_inj
  let θ : F →+* F' := IsFractionRing.lift (A := PowerSeries R) (K := F) (g := alg'.comp ι) hcomp_inj
  have hθ_alg : ∀ a : PowerSeries R, θ (algebraMap (PowerSeries R) F a) = alg' (ι a) := fun a =>
    IsFractionRing.lift_algebraMap hcomp_inj a
  have hθ_comp : θ.comp (algebraMap (PowerSeries R) F) = alg'.comp ι := RingHom.ext hθ_alg
  have hθ_inj : Function.Injective θ := θ.injective
  obtain ⟨u, hu⟩ := hmul
  set x : F := algebraMap (PowerSeries R) F u / algebraMap (PowerSeries R) F h with hx
  have hιh : ι h ≠ 0 := fun h' => h0 (hι_inj (by rw [h', map_zero]))
  have halg'h : alg' (ι h) ≠ 0 := fun h' => hιh (halg'_inj (by rw [h', map_zero]))
  have hθx : θ x = alg' g := by
    rw [hx, map_div₀, hθ_alg, hθ_alg, div_eq_iff halg'h, ← map_mul, mul_comm, ← hu]
  have hint : IsIntegral (PowerSeries R) x := by
    refine ⟨Φ, hΦ, ?_⟩
    apply hθ_inj
    rw [Polynomial.hom_eval₂, hθ_comp, hθx, map_zero, ← Polynomial.hom_eval₂, hroot, map_zero]
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  refine ⟨p, halg'_inj ?_⟩
  change alg' (ι p) = alg' g
  rw [← hθ_alg, hp, hθx]
/--
[PowerSeries_mem_range_map_of_monic_of_mul_mem_range](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PowerSeries_mem_range_map_of_monic_of_mul_mem_range.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  (g : PowerSeries K) (Φ : Polynomial (PowerSeries R)) (hΦ : Φ.Monic)
  (hroot : Polynomial.eval₂ (PowerSeries.map (algebraMap R K)) g Φ = 0)
  (h : PowerSeries R) (h0 : h ≠ 0)
  (hmul : PowerSeries.map (algebraMap R K) h * g ∈ (PowerSeries.map (algebraMap R K)).range) :
  -- imply
  g ∈ (PowerSeries.map (algebraMap R K)).range :=
  helper_main g Φ hΦ hroot h h0 hmul


-- created on 2026-10-20
