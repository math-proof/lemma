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
import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part6


namespace MetaMathlibExt

lemma r3leg_red_lift {p : ℕ} (w : r3legModVec p) :
    r3legRed p (r3legLift w) = w := by
  apply Prod.ext
  · apply Prod.ext <;> simp [r3legRed, r3legLift, ZMod.coe_valMinAbs]
  · simp [r3legRed, r3legLift, ZMod.coe_valMinAbs]

lemma r3leg_pure_aligned {p : ℕ} (u : r3legIntVec)
    (hu : r3legQ (r3legRed p u) = 0) :
    r3legAligned p (r3legPure u) (r3legRed p u) := by
  intro x
  refine ⟨2 * r3legB (r3legRed p x) (r3legRed p u), ?_⟩
  apply Prod.ext
  · apply Prod.ext
    · change ((r3legPhi (r3legPure u) x).1.1 : ZMod p) =
        (2 * r3legB (r3legRed p x) (r3legRed p u)) * (u.1.1 : ZMod p)
      rw [r3leg_phi_fst_fst]
      simp only [r3legPure]
      push_cast
      dsimp [r3legB, r3legRed, r3legQ] at hu ⊢
      linear_combination -(x.1.1 : ZMod p) * hu
    · change ((r3legPhi (r3legPure u) x).1.2 : ZMod p) =
        (2 * r3legB (r3legRed p x) (r3legRed p u)) * (u.1.2 : ZMod p)
      rw [r3leg_phi_fst_snd]
      simp only [r3legPure]
      push_cast
      dsimp [r3legB, r3legRed, r3legQ] at hu ⊢
      linear_combination -(x.1.2 : ZMod p) * hu
  · change ((r3legPhi (r3legPure u) x).2 : ZMod p) =
      (2 * r3legB (r3legRed p x) (r3legRed p u)) * (u.2 : ZMod p)
    rw [r3leg_phi_snd]
    simp only [r3legPure]
    push_cast
    dsimp [r3legB, r3legRed, r3legQ] at hu ⊢
    linear_combination -(x.2 : ZMod p) * hu

lemma r3leg_valMinAbs_sq_le {p : ℕ} [NeZero p] (a : ZMod p) :
    a.valMinAbs ^ 2 ≤ ((p / 2 : ℕ) : ℤ) ^ 2 := by
  have h := ZMod.natAbs_valMinAbs_le a
  have hsq := Nat.pow_le_pow_left h 2
  rw [← Int.natAbs_sq]
  exact_mod_cast hsq

lemma r3leg_initial_aligned_factor {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legModVec p) (hwne : w ≠ 0) (hwq : r3legQ w = 0) :
    ∃ m : ℕ, ∃ q : Quaternion ℤ,
      0 < m ∧ m < p ∧ Quaternion.normSq q = (m : ℤ) * p ∧
      r3legAligned p q w := by
  let u := r3legLift w
  let q := r3legPure u
  have hred : r3legRed p u = w := r3leg_red_lift w
  have huq : r3legQ (r3legRed p u) = 0 := by rw [hred]; exact hwq
  have hune : u ≠ 0 := by
    intro hu
    apply hwne
    rw [← hred, hu]
    simp [r3legRed]
  have hqne : q ≠ 0 := by
    intro hq
    apply hune
    have hI := congrArg (fun a : Quaternion ℤ => a.imI) hq
    have hJ := congrArg (fun a : Quaternion ℤ => a.imJ) hq
    have hK := congrArg (fun a : Quaternion ℤ => a.imK) hq
    exact Prod.ext (Prod.ext (by simpa [q, r3legPure] using hI)
      (by simpa [q, r3legPure] using hJ)) (by simpa [q, r3legPure] using hK)
  have hnormpos : 0 < Quaternion.normSq q := by
    have hnonneg : 0 ≤ Quaternion.normSq q := Quaternion.normSq_nonneg
    have hne : Quaternion.normSq q ≠ 0 := mt Quaternion.normSq_eq_zero.mp hqne
    omega
  have hpdvd : (p : ℤ) ∣ Quaternion.normSq q := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [r3leg_normSq_pure]
    dsimp [r3legQ, r3legRed] at huq ⊢
    push_cast
    exact huq
  have hnormlt : Quaternion.normSq q < (p : ℤ) ^ 2 := by
    have h₁ := r3leg_valMinAbs_sq_le w.1.1
    have h₂ := r3leg_valMinAbs_sq_le w.1.2
    have h₃ := r3leg_valMinAbs_sq_le w.2
    have hhalf : 2 * (p / 2) ≤ p := Nat.mul_div_le p 2
    rw [r3leg_normSq_pure, r3legQ]
    dsimp [q, u, r3legLift]
    have hhalf' : (2 : ℤ) * (p / 2 : ℕ) ≤ p := by exact_mod_cast hhalf
    have hp' : (3 : ℤ) ≤ p := by exact_mod_cast hp3
    nlinarith
  obtain ⟨t, ht⟩ := hpdvd
  have htpos : 0 < t := by
    have hp : (0 : ℤ) < p := by exact_mod_cast (show 0 < p by omega)
    nlinarith
  let m := t.natAbs
  have htcast : (m : ℤ) = t := Int.natAbs_of_nonneg (le_of_lt htpos)
  have hmpos : 0 < m := Int.natAbs_pos.mpr (ne_of_gt htpos)
  have htlt : t < (p : ℤ) := by
    have hp : (0 : ℤ) < p := by exact_mod_cast (show 0 < p by omega)
    nlinarith
  have hmlt : m < p := by
    have : (m : ℤ) < (p : ℤ) := by rw [htcast]; exact htlt
    exact_mod_cast this
  refine ⟨m, q, hmpos, hmlt, ?_, ?_⟩
  · rw [ht, htcast]
    ring
  · rw [← hred]
    exact r3leg_pure_aligned u huq

lemma r3leg_descend_to_one {p m : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legModVec p) (q : Quaternion ℤ)
    (hmpos : 0 < m) (hmp : m < p)
    (hnorm : Quaternion.normSq q = (m : ℤ) * p)
    (halign : r3legAligned p q w) :
    ∃ π : Quaternion ℤ, Quaternion.normSq π = p ∧ r3legAligned p π w := by
  induction m using Nat.strong_induction_on generalizing q with
  | h m ih =>
      by_cases hm1 : m = 1
      · subst m
        refine ⟨q, ?_, halign⟩
        simpa using hnorm
      rcases Nat.even_or_odd m with heven | hodd
      · have hm2 : 2 ∣ m := heven.two_dvd
        obtain ⟨q', hnorm', hmpos', hmlt, halign'⟩ :=
          r3leg_descend_even hp3 q w hmpos hm2 hnorm halign
        exact ih (m / 2) hmlt q' hmpos' (lt_trans hmlt hmp) hnorm' halign'
      · have hm3 : 3 ≤ m := by
          obtain ⟨k, hk⟩ := hodd.exists_bit1
          omega
        obtain ⟨m', q', hmpos', hmlt, hnorm', halign'⟩ :=
          r3leg_descend_odd q w hm3 hmp hodd hnorm halign
        exact ih m' hmlt q' hmpos' (lt_trans hmlt hmp) hnorm' halign'

lemma r3leg_aligned_norm_prime {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (w : r3legModVec p) (hwne : w ≠ 0) (hwq : r3legQ w = 0) :
    ∃ π : Quaternion ℤ, Quaternion.normSq π = p ∧ r3legAligned p π w := by
  obtain ⟨m, q, hmpos, hmp, hnorm, halign⟩ :=
    r3leg_initial_aligned_factor hp3 w hwne hwq
  exact r3leg_descend_to_one hp3 w q hmpos hmp hnorm halign

end MetaMathlibExt
