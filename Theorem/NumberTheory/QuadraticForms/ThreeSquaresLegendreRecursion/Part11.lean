/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.Basic
import Def.NumberTheory.QuadraticForms.ThreeSquares
import Lemma.Nat.QuadraticForms.ThreeSquares
import Mathlib.Algebra.Quaternion
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.FieldTheory.Finite.Basic
import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part11


namespace MetaMathlibExt

lemma r3leg_cast_b (p : ℕ) (x y : r3legIntVec) :
    ((r3legB x y : ℤ) : ZMod p) = r3legB (r3legRed p x) (r3legRed p y) := by
  simp [r3legB, r3legRed]

lemma r3leg_psi_red_eq_zero_iff {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) (x : r3legIntVec) :
    r3legRed p (r3legPhi (star (r3legPi hp3 w)) x) = 0 ↔
      r3legB (r3legRed p x) w = 0 := by
  let π := r3legPi hp3 w
  have hnorm : Quaternion.normSq π = p := r3legPi_norm hp3 w
  have halign : r3legAligned p π w := r3legPi_aligned hp3 w
  constructor
  · intro hpsi
    obtain ⟨e, _, _, he⟩ := r3leg_nonzero_column hp3 π hnorm
    obtain ⟨μ, hμ⟩ := halign e
    have hμne : μ ≠ 0 := by
      intro h
      apply he
      rw [hμ, h]
      simp
    have hzero : ((r3legB (r3legPhi (star π) x) e : ℤ) : ZMod p) = 0 := by
      rw [r3leg_cast_b, hpsi]
      simp [r3legB]
    rw [r3leg_phi_adjoint] at hzero
    rw [r3leg_cast_b, hμ] at hzero
    have hmul : μ * r3legB (r3legRed p x) w = 0 := by
      dsimp [r3legB] at hzero ⊢
      linear_combination hzero
    exact (mul_eq_zero.mp hmul).resolve_left hμne
  · intro hb
    apply Prod.ext
    · apply Prod.ext
      · obtain ⟨μ, hμ⟩ := halign r3legE₁
        change ((r3legPhi (star π) x).1.1 : ZMod p) = 0
        calc
          ((r3legPhi (star π) x).1.1 : ZMod p) =
              ((r3legB (r3legPhi (star π) x) r3legE₁ : ℤ) : ZMod p) := by
            simp [r3legB, r3legE₁]
          _ = ((r3legB x (r3legPhi π r3legE₁) : ℤ) : ZMod p) := by
            rw [r3leg_phi_adjoint]
          _ = r3legB (r3legRed p x) (r3legRed p (r3legPhi π r3legE₁)) :=
            r3leg_cast_b p _ _
          _ = 0 := by
            rw [hμ]
            dsimp [r3legB] at hb ⊢
            linear_combination μ * hb
      · obtain ⟨μ, hμ⟩ := halign r3legE₂
        change ((r3legPhi (star π) x).1.2 : ZMod p) = 0
        calc
          ((r3legPhi (star π) x).1.2 : ZMod p) =
              ((r3legB (r3legPhi (star π) x) r3legE₂ : ℤ) : ZMod p) := by
            simp [r3legB, r3legE₂]
          _ = ((r3legB x (r3legPhi π r3legE₂) : ℤ) : ZMod p) := by
            rw [r3leg_phi_adjoint]
          _ = r3legB (r3legRed p x) (r3legRed p (r3legPhi π r3legE₂)) :=
            r3leg_cast_b p _ _
          _ = 0 := by
            rw [hμ]
            dsimp [r3legB] at hb ⊢
            linear_combination μ * hb
    · obtain ⟨μ, hμ⟩ := halign r3legE₃
      change ((r3legPhi (star π) x).2 : ZMod p) = 0
      calc
        ((r3legPhi (star π) x).2 : ZMod p) =
            ((r3legB (r3legPhi (star π) x) r3legE₃ : ℤ) : ZMod p) := by
          simp [r3legB, r3legE₃]
        _ = ((r3legB x (r3legPhi π r3legE₃) : ℤ) : ZMod p) := by
          rw [r3leg_phi_adjoint]
        _ = r3legB (r3legRed p x) (r3legRed p (r3legPhi π r3legE₃)) :=
          r3leg_cast_b p _ _
        _ = 0 := by
          rw [hμ]
          dsimp [r3legB] at hb ⊢
          linear_combination μ * hb

lemma r3leg_vecDvd_iff_red_eq_zero (p : ℕ) (x : r3legIntVec) :
    r3legVecDvd (p : ℤ) x ↔ r3legRed p x = 0 := by
  constructor
  · intro h
    obtain ⟨h₁, h₂, h₃⟩ := h
    apply Prod.ext
    · apply Prod.ext
      · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h₁
      · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h₂
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h₃
  · intro h
    have h₁ := congrArg (fun z : r3legModVec p => z.1.1) h
    have h₂ := congrArg (fun z : r3legModVec p => z.1.2) h
    have h₃ := congrArg (fun z : r3legModVec p => z.2) h
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h₁,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h₂,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h₃⟩

lemma r3leg_sq_dvd_mul_iff {p : ℕ} (hp : 0 < p) (a : ℤ) :
    (p : ℤ) ^ 2 ∣ (p : ℤ) * a ↔ (p : ℤ) ∣ a := by
  constructor
  · intro h
    apply Int.dvd_of_mul_dvd_mul_left (a := (p : ℤ)) (m := (p : ℤ))
      (n := a) (by exact_mod_cast (show p ≠ 0 by omega))
    simpa [pow_two] using h
  · rintro ⟨k, rfl⟩
    refine ⟨k, by ring⟩

lemma r3leg_inc_scale_iff {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) (x : r3legIntVec) :
    r3legInc hp3 w (r3legScale p x) ↔ r3legB (r3legRed p x) w = 0 := by
  rw [r3legInc, r3leg_phi_scale]
  have hp : 0 < p := by omega
  have hdiv :
      r3legVecDvd ((p : ℤ) ^ 2)
          (r3legScale p (r3legPhi (star (r3legPi hp3 w)) x)) ↔
        r3legVecDvd (p : ℤ) (r3legPhi (star (r3legPi hp3 w)) x) := by
    simp only [r3legVecDvd, r3legScale]
    exact and_congr (r3leg_sq_dvd_mul_iff hp _)
      (and_congr (r3leg_sq_dvd_mul_iff hp _) (r3leg_sq_dvd_mul_iff hp _))
  rw [hdiv, r3leg_vecDvd_iff_red_eq_zero,
    r3leg_psi_red_eq_zero_iff hp3 w x]

lemma r3leg_inc_primitive_forward {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) (y : r3legIntVec)
    (hyne : r3legRed p y ≠ 0) (hinc : r3legInc hp3 w y) :
    ∃ κ : ZMod p, κ ≠ 0 ∧ r3legRed p y = κ • (w : r3legModVec p) := by
  let π := r3legPi hp3 w
  have hnorm : Quaternion.normSq π = p := r3legPi_norm hp3 w
  have halign : r3legAligned p π w := r3legPi_aligned hp3 w
  let x := r3legVecDiv (r3legPhi (star π) y) ((p : ℤ) ^ 2)
  have hscale : r3legScale ((p : ℤ) ^ 2) x = r3legPhi (star π) y := by
    exact r3leg_scale_vecDiv hinc
  have happly := congrArg (r3legPhi π) hscale
  rw [r3leg_phi_scale, r3leg_phi_star_phi, hnorm] at happly
  have hp2 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
  have hphi : r3legPhi π x = y := r3leg_scale_left_cancel hp2 happly
  obtain ⟨κ, hκ⟩ := halign x
  refine ⟨κ, ?_, ?_⟩
  · intro hκ0
    apply hyne
    rw [← hphi, hκ, hκ0]
    simp
  · rw [← hphi]
    exact hκ

lemma r3leg_vecDvd_add_scale_sq (p k : ℤ) (e v : r3legIntVec)
    (hv : r3legVecDvd p v) :
    r3legVecDvd (p ^ 2)
      (r3legAdd (r3legScale k (r3legScale (p ^ 2) e)) (r3legScale p v)) := by
  obtain ⟨⟨v₁, hv₁⟩, ⟨v₂, hv₂⟩, v₃, hv₃⟩ := hv
  constructor
  · refine ⟨k * e.1.1 + v₁, ?_⟩
    simp only [r3legAdd, r3legScale]
    rw [hv₁]
    ring
  constructor
  · refine ⟨k * e.1.2 + v₂, ?_⟩
    simp only [r3legAdd, r3legScale]
    rw [hv₂]
    ring
  · refine ⟨k * e.2 + v₃, ?_⟩
    simp only [r3legAdd, r3legScale]
    rw [hv₃]
    ring

lemma r3leg_inc_primitive_backward {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) (y : r3legIntVec)
    (hyq : r3legQ y = (p ^ 2 * n : ℕ)) {κ : ZMod p} (hκne : κ ≠ 0)
    (hyred : r3legRed p y = κ • (w : r3legModVec p)) : r3legInc hp3 w y := by
  let π := r3legPi hp3 w
  have hnorm : Quaternion.normSq π = p := r3legPi_norm hp3 w
  have halign : r3legAligned p π w := r3legPi_aligned hp3 w
  obtain ⟨e, _, heq, hecol⟩ := r3leg_nonzero_column hp3 π hnorm
  let a := r3legPhi π e
  obtain ⟨μ, hμ⟩ := halign e
  have hμne : μ ≠ 0 := by
    intro h
    apply hecol
    rw [hμ, h]
    simp
  let k : ℤ := (κ * μ⁻¹).valMinAbs
  have hkcast : (k : ZMod p) = κ * μ⁻¹ := ZMod.coe_valMinAbs _
  let d := r3legSub y (r3legScale k a)
  have hdred : r3legRed p d = 0 := by
    dsimp [d]
    rw [r3leg_red_sub, r3leg_red_scale, hyred]
    change r3legSub (κ • (w : r3legModVec p))
      ((k : ZMod p) • r3legRed p a) = 0
    rw [show r3legRed p a = μ • (w : r3legModVec p) by exact hμ, hkcast]
    apply Prod.ext
    · apply Prod.ext <;> simp [r3legSub, smul_smul, hμne]
    · simp [r3legSub, smul_smul, hμne]
  have hddiv : r3legVecDvd (p : ℤ) d :=
    (r3leg_vecDvd_iff_red_eq_zero p d).mpr hdred
  let z := r3legVecDiv d p
  have hzscale : r3legScale p z = d := r3leg_scale_vecDiv hddiv
  have hydecomp : y = r3legAdd (r3legScale k a) (r3legScale p z) := by
    apply Prod.ext
    · apply Prod.ext
      · have h := congrArg (fun v : r3legIntVec => v.1.1) hzscale
        dsimp [d, r3legScale, r3legSub, r3legAdd] at h ⊢
        linear_combination -h
      · have h := congrArg (fun v : r3legIntVec => v.1.2) hzscale
        dsimp [d, r3legScale, r3legSub, r3legAdd] at h ⊢
        linear_combination -h
    · have h := congrArg (fun v : r3legIntVec => v.2) hzscale
      dsimp [d, r3legScale, r3legSub, r3legAdd] at h ⊢
      linear_combination -h
  have haq : r3legQ a = (p : ℤ) ^ 2 := by
    dsimp [a]
    rw [r3leg_q_phi, hnorm, heq]
    ring
  have hq := congrArg r3legQ hydecomp
  rw [r3leg_q_add_scaled, hyq, haq] at hq
  push_cast at hq
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hcancel :
      (p : ℤ) * (2 * k * r3legB a z) =
        (p : ℤ) * ((p : ℤ) * ((n : ℤ) - k ^ 2 - r3legQ z)) := by
    linear_combination -hq
  have hmiddle : 2 * k * r3legB a z =
      (p : ℤ) * ((n : ℤ) - k ^ 2 - r3legQ z) :=
    mul_left_cancel₀ hpne hcancel
  have hbdvd : (p : ℤ) ∣ 2 * k * r3legB a z :=
    ⟨(n : ℤ) - k ^ 2 - r3legQ z, hmiddle⟩
  have hprod : (((2 * k * r3legB a z : ℤ) : ZMod p)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hbdvd
  push_cast at hprod
  have hkne : (k : ZMod p) ≠ 0 := by
    rw [hkcast]
    exact mul_ne_zero hκne (inv_ne_zero hμne)
  have h2kne : (2 : ZMod p) * (k : ZMod p) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast r3leg_two_ne_zero hp3) hkne
  have hbcast : ((r3legB a z : ℤ) : ZMod p) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left h2kne
  rw [r3leg_cast_b, hμ] at hbcast
  have hmub : μ * r3legB (r3legRed p z) w = 0 := by
    dsimp [r3legB] at hbcast ⊢
    linear_combination hbcast
  have hbzw : r3legB (r3legRed p z) w = 0 :=
    (mul_eq_zero.mp hmub).resolve_left hμne
  have hpsiz : r3legVecDvd (p : ℤ) (r3legPhi (star π) z) :=
    (r3leg_vecDvd_iff_red_eq_zero p _).mpr
      ((r3leg_psi_red_eq_zero_iff hp3 w z).mpr hbzw)
  have hpsia : r3legPhi (star π) a = r3legScale ((p : ℤ) ^ 2) e := by
    dsimp [a]
    rw [r3leg_phi_phi_star, hnorm]
  have hpsiy := congrArg (r3legPhi (star π)) hydecomp
  rw [r3leg_phi_add, r3leg_phi_scale, r3leg_phi_scale, hpsia] at hpsiy
  change r3legVecDvd ((p : ℤ) ^ 2) (r3legPhi (star π) y)
  rw [hpsiy]
  exact r3leg_vecDvd_add_scale_sq p k e (r3legPhi (star π) z) hpsiz

lemma r3leg_inc_primitive_iff {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legIso p) (y : r3legIntVec)
    (hyq : r3legQ y = (p ^ 2 * n : ℕ)) (hyne : r3legRed p y ≠ 0) :
    r3legInc hp3 w y ↔
      ∃ κ : ZMod p, κ ≠ 0 ∧ r3legRed p y = κ • (w : r3legModVec p) := by
  constructor
  · exact r3leg_inc_primitive_forward hp3 w y hyne
  · rintro ⟨κ, hκ, hy⟩
    exact r3leg_inc_primitive_backward hp3 w y hyq hκ hy

end MetaMathlibExt
