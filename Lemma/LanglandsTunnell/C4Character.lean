import Lemma.LanglandsTunnell.C8Character
import Instance.LanglandsTunnell_QuatH

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.P2

open NumberField IsDedekindDomain

section C4Sub

variable {L : Type*} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))

theorem gammaT_sq_mem_c8H : gammaT e ^ 2 ∈ c8H e :=
  Subgroup.pow_mem _ (gammaT_mem e) 2

def c4H : Subgroup (L ≃ₐ[ℚ] L) := Subgroup.zpowers (gammaT e ^ 2)

theorem mem_c4H_iff (γ : L ≃ₐ[ℚ] L) : γ ∈ c4H e ↔ ∃ k : ℤ, (gammaT e ^ 2) ^ k = γ :=
  Subgroup.mem_zpowers_iff

theorem c4H_le_c8H : c4H e ≤ c8H e :=
  (Subgroup.zpowers_le (G := L ≃ₐ[ℚ] L)).2 (gammaT_sq_mem_c8H e)

theorem orderOf_gammaT_sq : orderOf (gammaT e ^ 2) = 4 := by
  rw [orderOf_pow, orderOf_gammaT]
  decide

theorem card_c4H : Nat.card ↥(c4H e) = 4 := by
  rw [c4H, Nat.card_zpowers, orderOf_gammaT_sq]

def gammaTSqMem : ↥(c4H e) := ⟨gammaT e ^ 2, Subgroup.mem_zpowers _⟩

theorem orderOf_gammaTSqMem : orderOf (gammaTSqMem e) = 4 := by
  rw [← orderOf_injective (c4H e).subtype Subtype.coe_injective (gammaTSqMem e)]
  exact orderOf_gammaT_sq e

theorem mem_zpowers_gammaTSqMem (x : ↥(c4H e)) : x ∈ Subgroup.zpowers (gammaTSqMem e) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.2
  exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩

def c4H_inclusion : ↥(c4H e) →* ↥(c8H e) := Subgroup.inclusion (c4H_le_c8H e)

theorem c4H_inclusion_gammaTSqMem : c4H_inclusion e (gammaTSqMem e) = gammaTMem e ^ 2 :=
  Subtype.ext rfl

end C4Sub

section ChiGal4

variable {L : Type*} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
  {ζ : ℂ} (hζ : ζ ^ 4 = -1)

def chiGal4 : ↥(c4H e) →* ℂˣ := (chiGal e hζ).comp (c4H_inclusion e)

theorem chiGal4_apply (x : ↥(c4H e)) : chiGal4 e hζ x = chiGal e hζ (c4H_inclusion e x) := rfl

theorem chiGal4_gammaTSqMem : chiGal4 e hζ (gammaTSqMem e) = zetaUnit hζ ^ 2 := by
  rw [chiGal4_apply, c4H_inclusion_gammaTSqMem, map_pow, chiGal_gammaTMem]

include hζ in
theorem zetaUnit_sq_pow_two_ne_one : (zetaUnit hζ ^ 2) ^ 2 ≠ 1 := by
  rw [← pow_mul]
  exact zetaUnit_pow_four_ne_one hζ

theorem orderOf_zetaUnit_sq : orderOf (zetaUnit hζ ^ 2) = 4 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := zetaUnit hζ ^ 2) (zetaUnit_sq_pow_two_ne_one hζ)
    (by rw [← pow_mul]; exact zetaUnit_pow_eight hζ)
  norm_num at h
  exact h

theorem chiGal4_injective : Function.Injective (chiGal4 e hζ) := by
  refine (injective_iff_map_eq_one (chiGal4 e hζ)).2 fun x hx => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_gammaTSqMem e x)
  rw [map_zpow, chiGal4_gammaTSqMem] at hx
  have hdvd : (4 : ℤ) ∣ k := by
    rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_zetaUnit_sq] at hx
    exact_mod_cast hx
  rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_gammaTSqMem]
  exact_mod_cast hdvd

end ChiGal4

section Artin4

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
  (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {ζ : ℂ} (hζ : ζ ^ 4 = -1)

def artinValue4 (v : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L))) : ℂˣ :=
  chiGal4 e hζ ⟨seedFrob (c4H e) v, seedFrob_mem (c4H e) v⟩

theorem artinValue4_def (v : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L))) :
    artinValue4 e hζ v = chiGal4 e hζ ⟨seedFrob (c4H e) v, seedFrob_mem (c4H e) v⟩ := rfl

end Artin4

section QuatHContainment

open FLT.ExplicitLift LanglandsTunnell.Lift48 LanglandsTunnell

variable {L : Type} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))

theorem pw_Tlift_two_mem_P16 : pw Tlift 2 ∈ P16 := by
  rw [pw_eq_pow, pow_two]
  exact P16_mul_closed Tlift one_mem_P16.2.1 Tlift one_mem_P16.2.1

theorem gammaT_sq_mem_sylowH : gammaT e ^ 2 ∈ sylowH e :=
  ⟨pw Tlift 2, pw_Tlift_two_mem_P16, by
    rw [map_pow, e_gammaT, val_tbarGL_pow, ← pw_eq_pow, RingHom.mapMatrix_apply]⟩

theorem gammaT_sq_mem_detKer : gammaT e ^ 2 ∈ detKer e := by
  rw [mem_detKer_iff, map_pow, e_gammaT, val_tbarGL_pow, ← pw_eq_pow]
  decide

theorem c4H_le_quatH : c4H e ≤ quatH e :=
  (Subgroup.zpowers_le (G := L ≃ₐ[ℚ] L)).2 ⟨gammaT_sq_mem_sylowH e, gammaT_sq_mem_detKer e⟩

end QuatHContainment

section TowerInstances

open LanglandsTunnell

variable {L : Type} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))

theorem fixFld_c8H_le_fixFld_c4H : fixFld (c8H e) ≤ fixFld (c4H e) :=
  fixFld_le_fixFld_of_le (c4H_le_c8H e)


theorem fixFld_quatH_le_fixFld_c4H : fixFld (quatH e) ≤ fixFld (c4H e) :=
  fixFld_le_fixFld_of_le (c4H_le_quatH e)


end TowerInstances

section SynthProbe

open LanglandsTunnell
variable {L : Type} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
noncomputable example : Algebra (𝓞 ↥(fixFld (c8H e))) (𝓞 ↥(fixFld (c4H e))) := inferInstance
noncomputable example : Algebra.IsIntegral (𝓞 ↥(fixFld (c8H e))) (𝓞 ↥(fixFld (c4H e))) := inferInstance
noncomputable example : Algebra (𝓞 ↥(fixFld (quatH e))) (𝓞 ↥(fixFld (c4H e))) := inferInstance
noncomputable example : Algebra.IsIntegral (𝓞 ↥(fixFld (quatH e))) (𝓞 ↥(fixFld (c4H e))) := inferInstance
end SynthProbe

end LanglandsTunnell.P2

end
