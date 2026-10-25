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
import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part5


namespace MetaMathlibExt

lemma r3leg_bmod_cast (z : ℤ) (m : ℕ) :
    ((z.bmod m : ℤ) : ZMod m) = (z : ZMod m) := by
  apply (ZMod.intCast_eq_intCast_iff _ _ _).mpr
  exact Int.bmod_emod

lemma r3leg_norm_bmod_dvd (q : Quaternion ℤ) (m p : ℕ)
    (hnorm : Quaternion.normSq q = (m : ℤ) * p) :
    (m : ℤ) ∣ Quaternion.normSq (r3legQuatBmod q m) := by
  have hz : ((Quaternion.normSq q : ℤ) : ZMod m) = 0 := by
    rw [hnorm]
    push_cast
    simp
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  rw [Quaternion.normSq_def']
  push_cast
  simp only [r3legQuatBmod, r3leg_bmod_cast]
  rw [Quaternion.normSq_def'] at hz
  push_cast at hz
  exact hz

lemma r3leg_norm_bmod_ne_zero {p m : ℕ} [Fact (Nat.Prime p)]
    (q : Quaternion ℤ) (hm3 : 3 ≤ m) (hmp : m < p)
    (hnorm : Quaternion.normSq q = (m : ℤ) * p) :
    Quaternion.normSq (r3legQuatBmod q m) ≠ 0 := by
  intro hz
  have hqzero : r3legQuatBmod q m = 0 := Quaternion.normSq_eq_zero.mp hz
  have hre0 : q.re.bmod m = 0 := congrArg (fun a : Quaternion ℤ => a.re) hqzero
  have hI0 : q.imI.bmod m = 0 := congrArg (fun a : Quaternion ℤ => a.imI) hqzero
  have hJ0 : q.imJ.bmod m = 0 := congrArg (fun a : Quaternion ℤ => a.imJ) hqzero
  have hK0 : q.imK.bmod m = 0 := congrArg (fun a : Quaternion ℤ => a.imK) hqzero
  have hre : (m : ℤ) ∣ q.re := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [← r3leg_bmod_cast q.re m, hre0]
    simp
  have hI : (m : ℤ) ∣ q.imI := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [← r3leg_bmod_cast q.imI m, hI0]
    simp
  have hJ : (m : ℤ) ∣ q.imJ := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [← r3leg_bmod_cast q.imJ m, hJ0]
    simp
  have hK : (m : ℤ) ∣ q.imK := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [← r3leg_bmod_cast q.imK m, hK0]
    simp
  obtain ⟨a, ha⟩ := hre
  obtain ⟨b, hb⟩ := hI
  obtain ⟨c, hc⟩ := hJ
  obtain ⟨d, hd⟩ := hK
  have hsq : (m : ℤ) ^ 2 ∣ Quaternion.normSq q := by
    refine ⟨a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2, ?_⟩
    rw [Quaternion.normSq_def', ha, hb, hc, hd]
    ring
  rw [hnorm] at hsq
  have hmint : (m : ℤ) ∣ (p : ℤ) := by
    refine Int.dvd_of_mul_dvd_mul_left (a := (m : ℤ)) (m := (m : ℤ))
      (n := (p : ℤ)) ?_ ?_
    · exact_mod_cast (show m ≠ 0 by omega)
    · simpa [pow_two, mul_assoc] using hsq
  have hmnat : m ∣ p := by exact_mod_cast hmint
  rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd m hmnat with hm1 | hmp'
  · omega
  · omega

lemma r3leg_mul_star_bmod_dvd (q : Quaternion ℤ) (m : ℕ)
    (hr : (m : ℤ) ∣ Quaternion.normSq (r3legQuatBmod q m)) :
    (m : ℤ) ∣ (q * star (r3legQuatBmod q m)).re ∧
      (m : ℤ) ∣ (q * star (r3legQuatBmod q m)).imI ∧
      (m : ℤ) ∣ (q * star (r3legQuatBmod q m)).imJ ∧
      (m : ℤ) ∣ (q * star (r3legQuatBmod q m)).imK := by
  let r := r3legQuatBmod q m
  have hre : (r.re : ZMod m) = q.re := r3leg_bmod_cast q.re m
  have hI : (r.imI : ZMod m) = q.imI := r3leg_bmod_cast q.imI m
  have hJ : (r.imJ : ZMod m) = q.imJ := r3leg_bmod_cast q.imJ m
  have hK : (r.imK : ZMod m) = q.imK := r3leg_bmod_cast q.imK m
  have hrzero : ((Quaternion.normSq r : ℤ) : ZMod m) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hr
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star]
    push_cast
    rw [← hre, ← hI, ← hJ, ← hK]
    rw [Quaternion.normSq_def'] at hrzero
    push_cast at hrzero
    linear_combination hrzero
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Quaternion.imI_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star]
    push_cast
    rw [← hre, ← hI, ← hJ, ← hK]
    ring
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Quaternion.imJ_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star]
    push_cast
    rw [← hre, ← hI, ← hJ, ← hK]
    ring
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star]
    push_cast
    rw [← hre, ← hI, ← hJ, ← hK]
    ring

lemma r3leg_descend_odd {p m : ℕ} [Fact (Nat.Prime p)]
    (q : Quaternion ℤ) (w : r3legModVec p)
    (hm3 : 3 ≤ m) (hmp : m < p) (hodd : Odd m)
    (hnorm : Quaternion.normSq q = (m : ℤ) * p)
    (halign : r3legAligned p q w) :
    ∃ m' : ℕ, ∃ q' : Quaternion ℤ,
      0 < m' ∧ m' < m ∧ Quaternion.normSq q' = (m' : ℤ) * p ∧
      r3legAligned p q' w := by
  let r := r3legQuatBmod q m
  have hrdiv : (m : ℤ) ∣ Quaternion.normSq r := by
    simpa [r] using r3leg_norm_bmod_dvd q m p hnorm
  have hrne : Quaternion.normSq r ≠ 0 := by
    simpa [r] using r3leg_norm_bmod_ne_zero q hm3 hmp hnorm
  have hrpos : 0 < Quaternion.normSq r := by
    have hrnonneg : 0 ≤ Quaternion.normSq r := Quaternion.normSq_nonneg
    omega
  obtain ⟨k, hk⟩ := hodd.exists_bit1
  have hrlt : Quaternion.normSq r < (m : ℤ) ^ 2 := by
    have h₀ := r3leg_bmod_sq_le q.re k
    have h₁ := r3leg_bmod_sq_le q.imI k
    have h₂ := r3leg_bmod_sq_le q.imJ k
    have h₃ := r3leg_bmod_sq_le q.imK k
    rw [Quaternion.normSq_def']
    dsimp [r, r3legQuatBmod]
    rw [hk]
    push_cast
    nlinarith
  have hcoords := r3leg_mul_star_bmod_dvd q m (by simpa [r] using hrdiv)
  obtain ⟨t, ht⟩ := hrdiv
  have htpos : 0 < t := by
    have hmpos : (0 : ℤ) < m := by exact_mod_cast (show 0 < m by omega)
    nlinarith
  let m' := t.natAbs
  have htcast : (m' : ℤ) = t := by
    exact Int.natAbs_of_nonneg (le_of_lt htpos)
  have hm'pos : 0 < m' := Int.natAbs_pos.mpr (ne_of_gt htpos)
  have htlt : t < (m : ℤ) := by
    have hmpos : (0 : ℤ) < m := by exact_mod_cast (show 0 < m by omega)
    nlinarith
  have hm'lt : m' < m := by
    have hm'lt' : (m' : ℤ) < (m : ℤ) := by rw [htcast]; exact htlt
    exact_mod_cast hm'lt'
  have hrnorm : Quaternion.normSq r = (m : ℤ) * m' := by
    rw [ht, htcast]
  obtain ⟨hre, hI, hJ, hK⟩ := hcoords
  let q' := r3legQuatDiv (q * star r) m
  have hscale : (m : ℤ) • q' = q * star r := by
    exact r3leg_smul_quatDiv _ _ hre hI hJ hK
  have hnscale := congrArg Quaternion.normSq hscale
  rw [Quaternion.normSq_smul, map_mul, Quaternion.normSq_star, hnorm, hrnorm] at hnscale
  have hnorm' : Quaternion.normSq q' = (m' : ℤ) * p := by
    have hmpos : (0 : ℤ) < m := by exact_mod_cast (show 0 < m by omega)
    nlinarith
  have hmcast : ((m : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    have hnat : ((m : ℕ) : ZMod p) = 0 := by exact_mod_cast hz
    have hd : p ∣ m := (ZMod.natCast_eq_zero_iff m p).mp hnat
    have hple : p ≤ m := Nat.le_of_dvd (by omega) hd
    omega
  refine ⟨m', q', hm'pos, hm'lt, hnorm', ?_⟩
  exact r3leg_aligned_transfer hmcast hscale halign

end MetaMathlibExt
