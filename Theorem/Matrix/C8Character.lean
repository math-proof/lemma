module

public import Def.LanglandsTunnell_LiftTraceSeed
public import Theorem.Matrix.Lift48

public noncomputable section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.P2

open NumberField IsDedekindDomain FLT.ExplicitLift Matrix.Lift48


public theorem one_mem_C8 : (1 : Mat) ∈ C8 := by decide


public theorem Tlift_mem_C8 : Tlift ∈ C8 := by decide


public theorem C8_mul_closed : ∀ M ∈ C8, ∀ N ∈ C8, M * N ∈ C8 := by decide


public theorem C8_pw_seven_mem : ∀ M ∈ C8, pw M 7 ∈ C8 := by decide


public theorem C8_mul_pw_seven : ∀ M ∈ C8, M * pw M 7 = 1 := by decide


public theorem Tlift_det_eq_neg_one : Tlift.det = -1 := by
  rw [Matrix.det_fin_two]; decide


public theorem Tlift_pow_four_eq_neg_one : Tlift ^ 4 = -1 := by
  rw [← pw_eq_pow]; decide


public theorem Tlift_pow_eight_eq_one : Tlift ^ 8 = 1 := by
  rw [← pw_eq_pow]; decide

section C8Sub

variable {L : Type*} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))


public theorem mem_c8H_iff (γ : L ≃ₐ[ℚ] L) :
    γ ∈ c8H e ↔ ∃ M ∈ C8,
      M.map red = ((e γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) :=
  Iff.rfl


public theorem val_tbarGL : ((tbarGL : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))
    = red.mapMatrix Tlift := rfl


public theorem val_tbarGL_pow (k : ℕ) :
    ((tbarGL ^ k : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))
      = red.mapMatrix (Tlift ^ k) := by
  rw [Units.val_pow_eq_pow_val, val_tbarGL, map_pow]


public theorem tbarGL_pow_four_ne_one : tbarGL ^ 4 ≠ 1 := by
  intro h
  have h' := congrArg Units.val h
  rw [val_tbarGL_pow, Tlift_pow_four_eq_neg_one, map_neg, map_one, Units.val_one] at h'
  exact absurd h' (by decide)


public theorem tbarGL_pow_eight : tbarGL ^ 8 = 1 :=
  Units.ext (by rw [val_tbarGL_pow, Tlift_pow_eight_eq_one, map_one, Units.val_one])


public theorem orderOf_tbarGL : orderOf tbarGL = 8 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 2) (x := tbarGL) tbarGL_pow_four_ne_one tbarGL_pow_eight
  norm_num at h
  exact h


public theorem e_gammaT : e (gammaT e) = tbarGL := MulEquiv.apply_symm_apply e _


public theorem gammaT_mem : gammaT e ∈ c8H e :=
  ⟨Tlift, Tlift_mem_C8, by rw [e_gammaT]; rfl⟩


public theorem orderOf_gammaT : orderOf (gammaT e) = 8 := by
  have h := orderOf_injective e.toMonoidHom e.injective (gammaT e)
  rw [MulEquiv.coe_toMonoidHom, e_gammaT, orderOf_tbarGL] at h
  exact h.symm


public theorem exists_pow_gammaT_eq {γ : L ≃ₐ[ℚ] L} (hγ : γ ∈ c8H e) : ∃ k : ℕ, gammaT e ^ k = γ := by
  obtain ⟨M, hM, hMγ⟩ := hγ
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hM
  refine ⟨k, e.injective (Units.ext ?_)⟩
  rw [map_pow, e_gammaT, val_tbarGL_pow, ← pw_eq_pow, RingHom.mapMatrix_apply, hMγ]


public theorem orderOf_gammaTMem : orderOf (gammaTMem e) = 8 := by
  rw [← orderOf_injective (c8H e).subtype Subtype.coe_injective (gammaTMem e)]
  exact orderOf_gammaT e


public theorem mem_zpowers_gammaTMem (x : ↥(c8H e)) : x ∈ Subgroup.zpowers (gammaTMem e) := by
  obtain ⟨k, hk⟩ := exists_pow_gammaT_eq e x.2
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨(k : ℤ), Subtype.ext (by rw [zpow_natCast, Subgroup.coe_pow]; exact hk)⟩


public theorem c8H_eq_zpowers : c8H e = Subgroup.zpowers (gammaT e) := by
  refine le_antisymm (fun γ hγ => ?_) ((Subgroup.zpowers_le (G := L ≃ₐ[ℚ] L)).2 (gammaT_mem e))
  obtain ⟨k, rfl⟩ := exists_pow_gammaT_eq e hγ
  exact Subgroup.npow_mem_zpowers _ _


public theorem card_c8H : Nat.card ↥(c8H e) = 8 := by
  rw [c8H_eq_zpowers, Nat.card_zpowers, orderOf_gammaT]

end C8Sub

section ChiGal

variable {L : Type*} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
  {ζ : ℂ} (hζ : ζ ^ 4 = -1)

include hζ in

public theorem zeta_ne_zero : ζ ≠ 0 := by
  rintro rfl
  norm_num at hζ

include hζ in

public theorem zeta_pow_eight : ζ ^ 8 = 1 := by
  rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, hζ]
  norm_num


public theorem val_zetaUnit : ((zetaUnit hζ : ℂˣ) : ℂ) = ζ := rfl


public theorem zetaUnit_pow_eight : zetaUnit hζ ^ 8 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, val_zetaUnit, zeta_pow_eight hζ, Units.val_one])


public theorem orderOf_zetaUnit_dvd : orderOf (zetaUnit hζ) ∣ orderOf (gammaTMem e) := by
  rw [orderOf_gammaTMem]
  exact orderOf_dvd_of_pow_eq_one (zetaUnit_pow_eight hζ)


public theorem chiGal_gammaTMem : chiGal e hζ (gammaTMem e) = zetaUnit hζ :=
  monoidHomOfForallMemZpowers_apply_gen (mem_zpowers_gammaTMem e) (orderOf_zetaUnit_dvd e hζ)


public theorem chiGal_gammaT_pow (k : ℕ) : chiGal e hζ (gammaTMem e ^ k) = zetaUnit hζ ^ k := by
  rw [map_pow, chiGal_gammaTMem]


public theorem zetaUnit_pow_four_ne_one : zetaUnit hζ ^ 4 ≠ 1 := by
  intro h
  have h' := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, val_zetaUnit, hζ, Units.val_one] at h'
  norm_num at h'


public theorem orderOf_zetaUnit : orderOf (zetaUnit hζ) = 8 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 2) (x := zetaUnit hζ) (zetaUnit_pow_four_ne_one hζ)
    (zetaUnit_pow_eight hζ)
  norm_num at h
  exact h


public theorem chiGal_injective : Function.Injective (chiGal e hζ) := by
  refine (injective_iff_map_eq_one (chiGal e hζ)).2 fun x hx => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_gammaTMem e x)
  rw [map_zpow, chiGal_gammaTMem] at hx
  have hdvd : (8 : ℤ) ∣ k := by
    rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_zetaUnit] at hx
    exact_mod_cast hx
  rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_gammaTMem]
  exact_mod_cast hdvd

end ChiGal

section Artin

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
  (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {ζ : ℂ} (hζ : ζ ^ 4 = -1)

open Classical in


public theorem seedFrob_mem (H : Subgroup (L ≃ₐ[ℚ] L))
    (w : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L))) : seedFrob H w ∈ H := by
  unfold seedFrob relDeg
  exact (Nat.find_spec (exists_pos_pow_mem H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver H w)))).2


public theorem artinValue_def (v : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))) :
    artinValue e hζ v = chiGal e hζ ⟨seedFrob (c8H e) v, seedFrob_mem (c8H e) v⟩ := rfl

end Artin

end LanglandsTunnell.P2

end
