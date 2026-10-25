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
import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part7


namespace MetaMathlibExt

lemma r3leg_two_ne_zero {p : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
    ((2 : ℤ) : ZMod p) ≠ 0 := by
  intro h
  have hnat : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hnat
  have hp_le : p ≤ 2 := Nat.le_of_dvd (by decide) hd
  omega

lemma r3leg_nonzero_column {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (π : Quaternion ℤ) (hnorm : Quaternion.normSq π = p) :
    ∃ e : r3legIntVec,
      (e = r3legE₁ ∨ e = r3legE₂ ∨ e = r3legE₃) ∧
      r3legQ e = 1 ∧ r3legRed p (r3legPhi π e) ≠ 0 := by
  by_cases h₁ : r3legRed p (r3legPhi π r3legE₁) ≠ 0
  · exact ⟨r3legE₁, Or.inl rfl, by decide, h₁⟩
  by_cases h₂ : r3legRed p (r3legPhi π r3legE₂) ≠ 0
  · exact ⟨r3legE₂, Or.inr (Or.inl rfl), by decide, h₂⟩
  by_cases h₃ : r3legRed p (r3legPhi π r3legE₃) ≠ 0
  · exact ⟨r3legE₃, Or.inr (Or.inr rfl), by decide, h₃⟩
  have h₁' := not_ne_iff.mp h₁
  have h₂' := not_ne_iff.mp h₂
  have h₃' := not_ne_iff.mp h₃
  have hd₁ :
      ((π.re ^ 2 + π.imI ^ 2 - π.imJ ^ 2 - π.imK ^ 2 : ℤ) : ZMod p) = 0 := by
    have h := congrArg (fun v : r3legModVec p => v.1.1) h₁'
    change ((r3legPhi π r3legE₁).1.1 : ZMod p) = 0 at h
    rw [r3leg_phi_fst_fst] at h
    simpa [r3legE₁] using h
  have hd₂ :
      ((π.re ^ 2 - π.imI ^ 2 + π.imJ ^ 2 - π.imK ^ 2 : ℤ) : ZMod p) = 0 := by
    have h := congrArg (fun v : r3legModVec p => v.1.2) h₂'
    change ((r3legPhi π r3legE₂).1.2 : ZMod p) = 0 at h
    rw [r3leg_phi_fst_snd] at h
    simpa [r3legE₂] using h
  have hd₃ :
      ((π.re ^ 2 - π.imI ^ 2 - π.imJ ^ 2 + π.imK ^ 2 : ℤ) : ZMod p) = 0 := by
    have h := congrArg (fun v : r3legModVec p => v.2) h₃'
    change ((r3legPhi π r3legE₃).2 : ZMod p) = 0 at h
    rw [r3leg_phi_snd] at h
    simpa [r3legE₃] using h
  have hn :
      (π.re : ZMod p) ^ 2 + π.imI ^ 2 + π.imJ ^ 2 + π.imK ^ 2 = 0 := by
    have h := congrArg (fun z : ℤ => (z : ZMod p)) hnorm
    rw [Quaternion.normSq_def'] at h
    push_cast at h
    simpa using h
  push_cast at hd₁ hd₂ hd₃
  have htwo := r3leg_two_ne_zero hp3
  have hAB : (π.re : ZMod p) ^ 2 + π.imI ^ 2 = 0 := by
    have h : (2 : ZMod p) * ((π.re : ZMod p) ^ 2 + π.imI ^ 2) = 0 := by
      linear_combination hd₁ + hn
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast htwo)
  have hAC : (π.re : ZMod p) ^ 2 + π.imJ ^ 2 = 0 := by
    have h : (2 : ZMod p) * ((π.re : ZMod p) ^ 2 + π.imJ ^ 2) = 0 := by
      linear_combination hd₂ + hn
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast htwo)
  have hAD : (π.re : ZMod p) ^ 2 + π.imK ^ 2 = 0 := by
    have h : (2 : ZMod p) * ((π.re : ZMod p) ^ 2 + π.imK ^ 2) = 0 := by
      linear_combination hd₃ + hn
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast htwo)
  have hA : (π.re : ZMod p) ^ 2 = 0 := by
    have h : (2 : ZMod p) * (π.re : ZMod p) ^ 2 = 0 := by
      linear_combination hAB + hAC + hAD - hn
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast htwo)
  have hB : (π.imI : ZMod p) ^ 2 = 0 := by linear_combination hAB - hA
  have hC : (π.imJ : ZMod p) ^ 2 = 0 := by linear_combination hAC - hA
  have hD : (π.imK : ZMod p) ^ 2 = 0 := by linear_combination hAD - hA
  have ha0 : (π.re : ZMod p) = 0 := (sq_eq_zero_iff).mp hA
  have hb0 : (π.imI : ZMod p) = 0 := (sq_eq_zero_iff).mp hB
  have hc0 : (π.imJ : ZMod p) = 0 := (sq_eq_zero_iff).mp hC
  have hd0 : (π.imK : ZMod p) = 0 := (sq_eq_zero_iff).mp hD
  have ha : (p : ℤ) ∣ π.re := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ha0
  have hb : (p : ℤ) ∣ π.imI := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb0
  have hc : (p : ℤ) ∣ π.imJ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc0
  have hd : (p : ℤ) ∣ π.imK := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hd0
  obtain ⟨a, ha'⟩ := ha
  obtain ⟨b, hb'⟩ := hb
  obtain ⟨c, hc'⟩ := hc
  obtain ⟨d, hd'⟩ := hd
  have hsq : (p : ℤ) ^ 2 ∣ Quaternion.normSq π := by
    refine ⟨a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2, ?_⟩
    rw [Quaternion.normSq_def', ha', hb', hc', hd']
    ring
  rw [hnorm] at hsq
  have hpdiv : (p : ℤ) ∣ (1 : ℤ) := by
    refine Int.dvd_of_mul_dvd_mul_left (a := (p : ℤ)) (m := (p : ℤ))
      (n := 1) ?_ ?_
    · exact_mod_cast (show p ≠ 0 by omega)
    · simpa [pow_two] using hsq
  have hpdiv' : p ∣ 1 := by exact_mod_cast hpdiv
  have : p ≤ 1 := Nat.le_of_dvd (by decide) hpdiv'
  omega

lemma r3leg_phi_scale (q : Quaternion ℤ) (c : ℤ) (x : r3legIntVec) :
    r3legPhi q (r3legScale c x) = r3legScale c (r3legPhi q x) := by
  apply Prod.ext
  · apply Prod.ext
    · simp only [r3legScale]
      rw [r3leg_phi_fst_fst, r3leg_phi_fst_fst]
      ring
    · simp only [r3legScale]
      rw [r3leg_phi_fst_snd, r3leg_phi_fst_snd]
      ring
  · simp only [r3legScale]
    rw [r3leg_phi_snd, r3leg_phi_snd]
    ring

lemma r3leg_phi_add (q : Quaternion ℤ) (x y : r3legIntVec) :
    r3legPhi q (r3legAdd x y) = r3legAdd (r3legPhi q x) (r3legPhi q y) := by
  apply Prod.ext
  · apply Prod.ext
    · simp only [r3legAdd]
      rw [r3leg_phi_fst_fst, r3leg_phi_fst_fst, r3leg_phi_fst_fst]
      ring
    · simp only [r3legAdd]
      rw [r3leg_phi_fst_snd, r3leg_phi_fst_snd, r3leg_phi_fst_snd]
      ring
  · simp only [r3legAdd]
    rw [r3leg_phi_snd, r3leg_phi_snd, r3leg_phi_snd]
    ring

lemma r3leg_red_sub (p : ℕ) (x y : r3legIntVec) :
    r3legRed p (r3legSub x y) = r3legSub (r3legRed p x) (r3legRed p y) := by
  apply Prod.ext
  · apply Prod.ext <;> simp [r3legRed, r3legSub]
  · simp [r3legRed, r3legSub]

lemma r3leg_q_add_scaled (c d : ℤ) (x y : r3legIntVec) :
    r3legQ (r3legAdd (r3legScale c x) (r3legScale d y)) =
      c ^ 2 * r3legQ x + 2 * c * d * r3legB x y + d ^ 2 * r3legQ y := by
  simp only [r3legQ, r3legB, r3legAdd, r3legScale]
  ring

lemma r3leg_scale_left_cancel {c : ℤ} (hc : c ≠ 0) {x y : r3legIntVec}
    (h : r3legScale c x = r3legScale c y) : x = y := by
  have h₁ := congrArg (fun z : r3legIntVec => z.1.1) h
  have h₂ := congrArg (fun z : r3legIntVec => z.1.2) h
  have h₃ := congrArg (fun z : r3legIntVec => z.2) h
  simp only [r3legScale] at h₁ h₂ h₃
  exact Prod.ext (Prod.ext (mul_left_cancel₀ hc h₁) (mul_left_cancel₀ hc h₂))
    (mul_left_cancel₀ hc h₃)

lemma r3leg_phi_injective (q : Quaternion ℤ)
    (hnorm : Quaternion.normSq q ≠ 0) : Function.Injective (r3legPhi q) := by
  intro x y h
  have h' := congrArg (r3legPhi (star q)) h
  rw [r3leg_phi_phi_star, r3leg_phi_phi_star] at h'
  exact r3leg_scale_left_cancel (pow_ne_zero 2 hnorm) h'

end MetaMathlibExt
