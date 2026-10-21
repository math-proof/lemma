import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[W54_exists_padicInt_ringHom](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_W54_exists_padicInt_ringHom.lean)
-/
@[path]
private lemma main (p : ℕ) [Fact p.Prime]
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪']
    (hp𝒪' : (p : 𝒪') ∈ IsLocalRing.maximalIdeal 𝒪') :
    ∃ φ : ℤ_[p] →+* 𝒪', IsLocalHom φ := by
  classical
  have hchar : ∀ n : ℕ, ((p ^ n : ℕ) : 𝒪' ⧸ (IsLocalRing.maximalIdeal 𝒪') ^ n) = 0 := by
    intro n
    rw [← map_natCast (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪') ^ n)) (p ^ n),
      Ideal.Quotient.eq_zero_iff_mem]
    push_cast
    exact Ideal.pow_mem_pow hp𝒪' n
  have hdvd : ∀ n : ℕ, ringChar (𝒪' ⧸ (IsLocalRing.maximalIdeal 𝒪') ^ n) ∣ p ^ n := fun n =>
    (CharP.cast_eq_zero_iff (𝒪' ⧸ (IsLocalRing.maximalIdeal 𝒪') ^ n)
      (ringChar (𝒪' ⧸ (IsLocalRing.maximalIdeal 𝒪') ^ n)) (p ^ n)).mp (hchar n)
  have hcompat : ∀ (m n : ℕ), m ≤ n →
      ∀ g : (𝒪' ⧸ (IsLocalRing.maximalIdeal 𝒪') ^ n) →+*
            (𝒪' ⧸ (IsLocalRing.maximalIdeal 𝒪') ^ m),
      g.comp ((ZMod.castHom (hdvd n) (𝒪' ⧸ (IsLocalRing.maximalIdeal 𝒪') ^ n)).comp
          (PadicInt.toZModPow n)) =
        (ZMod.castHom (hdvd m) (𝒪' ⧸ (IsLocalRing.maximalIdeal 𝒪') ^ m)).comp
          (PadicInt.toZModPow m) := by
    intro m n hle g
    ext x
    have key := RingHom.congr_fun
      (RingHom.ext_zmod
        (g.comp (ZMod.castHom (hdvd n) (𝒪' ⧸ (IsLocalRing.maximalIdeal 𝒪') ^ n)))
        ((ZMod.castHom (hdvd m) (𝒪' ⧸ (IsLocalRing.maximalIdeal 𝒪') ^ m)).comp
          (ZMod.castHom (pow_dvd_pow p hle) (ZMod (p ^ m)))))
      (PadicInt.toZModPow n x)
    have key2 := RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow m n hle) x
    simp only [RingHom.coe_comp, Function.comp_apply] at key key2 ⊢
    rw [key, key2]
  refine ⟨IsAdicComplete.liftRingHom (IsLocalRing.maximalIdeal 𝒪')
      (fun n => (ZMod.castHom (hdvd n) (𝒪' ⧸ (IsLocalRing.maximalIdeal 𝒪') ^ n)).comp
        (PadicInt.toZModPow n))
      (fun {m n} hle => hcompat m n hle _), ?_⟩
  constructor
  intro a ha
  by_contra hna
  have hmem : a ∈ IsLocalRing.maximalIdeal ℤ_[p] := (IsLocalRing.mem_maximalIdeal a).mpr hna
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
  obtain ⟨b, rfl⟩ := hmem
  rw [map_mul, map_natCast] at ha
  exact (IsLocalRing.maximalIdeal.isMaximal 𝒪').ne_top
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.mul_mem_right _ _ hp𝒪') ha)

-- created on 2026-10-20
