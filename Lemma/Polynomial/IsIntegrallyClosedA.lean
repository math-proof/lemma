import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial


/--
[IsGaloisGroup_isIntegrallyClosed_of_isIntegrallyClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsGaloisGroup_isIntegrallyClosed_of_isIntegrallyClosed.lean)
-/
@[path]
private lemma main
  [Group G] [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B] [MulSemiringAction G B] [IsGaloisGroup G A B] [IsIntegrallyClosed B] :
-- imply
  IsIntegrallyClosed A := by
-- proof
  classical
    let K := FractionRing A
    let L := FractionRing B
    have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
    have hinjL : Function.Injective ((algebraMap B L).comp (algebraMap A B)) :=
      (IsFractionRing.injective B L).comp hinj
    let φ : K →+* L := IsFractionRing.lift hinjL
    have hφ : ∀ a : A, φ (algebraMap A K a) = algebraMap B L (algebraMap A B a) := fun a =>
      IsFractionRing.lift_algebraMap hinjL a
    refine (isIntegrallyClosed_iff K).mpr ?_
    intro x hx
    obtain ⟨a₁, a₂, ha₂, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    have ha₂0 : a₂ ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp ha₂
    have hfa₂ : algebraMap A B a₂ ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha₂0
    have hKa₂ : algebraMap A K a₂ ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha₂
    have hLa₂ : algebraMap B L (algebraMap A B a₂) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hfa₂
    have hint : IsIntegral B (φ (algebraMap A K a₁ / algebraMap A K a₂)) := by
      obtain ⟨p, hp, hpx⟩ := hx
      refine ⟨p.map (algebraMap A B), hp.map _, ?_⟩
      rw [eval₂_map]
      have hcomp : (algebraMap B L).comp (algebraMap A B) = φ.comp (algebraMap A K) := by
        ext a; simp [hφ]
      rw [hcomp, ← hom_eval₂, hpx, map_zero]
    obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := B) (K := L)).mp hint
    rw [map_div₀, hφ, hφ, eq_div_iff hLa₂, ← map_mul] at hb
    have hb' : b * algebraMap A B a₂ = algebraMap A B a₁ := IsFractionRing.injective B L hb
    have hfix : ∀ g : G, g • b = b := by
      intro g
      apply mul_right_cancel₀ hfa₂
      have h1 : g • (b * algebraMap A B a₂) = b * algebraMap A B a₂ := by
        rw [hb', smul_algebraMap]
      rwa [smul_mul', smul_algebraMap] at h1
    obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) b hfix
    refine ⟨a, ?_⟩
    have haa : a * a₂ = a₁ := hinj (by rw [map_mul, ha, hb'])
    rw [eq_div_iff hKa₂, ← map_mul, haa]


-- created on 2026-10-23
