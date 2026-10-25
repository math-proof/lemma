/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HilbertWaring.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Def.Combinatorics.Schnirelmann
import Lemma.Finset.Schnirelmann
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.PSeries
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic
import Def.NumberTheory.HilbertWaring.Part5
/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/


namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset

open scoped Pointwise

lemma hw_packCenteredNonzero_mem (H M : ℕ)
    (p : {p // p ∈ hwCenteredFourNonzero H M}) :
    hwPackCenteredNonzero H M p ∈
      (Finset.univ : Finset (hwPairData H M × hwPairData H M)).filter fun q ↦
        hwPairVal H M q.1 + hwPairVal H M q.2 = 0 := by
  have hs (i : Fin 4) :
      hwSignedVal H ((hwSignedEquivCentered H).symm
        ⟨p.1.1 i, (Finset.mem_filter.mp p.2).2.2 i⟩) =
        hwCentered H (p.1.1 i) := by
    rw [← hw_centered_signedToCentered]
    have he := (hwSignedEquivCentered H).apply_symm_apply
      ⟨p.1.1 i, (Finset.mem_filter.mp p.2).2.2 i⟩
    exact congrArg (fun z ↦ hwCentered H z.1) he
  have hp := (Finset.mem_filter.mp p.2).2.1
  simp only [Fin.sum_univ_succ] at hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  dsimp [hwPackCenteredNonzero, hwPairVal]
  rw [hs, hs, hs, hs]
  ring_nf at hp ⊢
  exact hp

lemma hw_centeredFourNonzero_card_le (H M : ℕ) :
    #(hwCenteredFourNonzero H M) ≤ hwFourTermCount H M := by
  let S := {p // p ∈ hwCenteredFourNonzero H M}
  let f : S → hwPairData H M × hwPairData H M := hwPackCenteredNonzero H M
  have himage : (Finset.univ : Finset S).image f ⊆
      (Finset.univ : Finset (hwPairData H M × hwPairData H M)).filter fun q ↦
        hwPairVal H M q.1 + hwPairVal H M q.2 = 0 := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, _, rfl⟩
    exact hw_packCenteredNonzero_mem H M p
  calc
    #(hwCenteredFourNonzero H M) = Fintype.card S := by
      dsimp [S]
      rw [Fintype.card_subtype]
      simp
    _ = #((Finset.univ : Finset S).image f) := by
      calc
        Fintype.card S = #(Finset.univ : Finset S) := by simp
        _ = #((Finset.univ : Finset S).image f) :=
          (Finset.card_image_of_injective Finset.univ
            (hw_packCenteredNonzero_injective H M)).symm
    _ ≤ #((Finset.univ : Finset (hwPairData H M × hwPairData H M)).filter fun q ↦
        hwPairVal H M q.1 + hwPairVal H M q.2 = 0) := Finset.card_le_card himage
    _ = hwFourTermCount H M := rfl

lemma hw_centeredFourTerm_card_le (H M : ℕ) :
    #(hwCenteredFourTerm H M) ≤
      hwFourTermCount H M + (2 * M + 1) ^ 4 +
        4 * (2 * H + 1) ^ 3 * (2 * M + 1) ^ 3 := by
  let F : (Fin 4 → Fin (2 * H + 1)) → ℕ := fun h ↦
    #(hwLinearFiber M fun i ↦ hwCentered H (h i))
  let P : (Fin 4 → Fin (2 * H + 1)) → Prop := fun h ↦
    ∀ i, hwCentered H (h i) ≠ 0
  let Q : (Fin 4 → Fin (2 * H + 1)) → Prop := fun h ↦
    ∃ i, hwCentered H (h i) = 0
  have hpart (h : Fin 4 → Fin (2 * H + 1)) :
      F h = (if P h then F h else 0) + if Q h then F h else 0 := by
    by_cases hp : P h
    · have hq : ¬Q h := fun hq ↦ by
        obtain ⟨i, hi⟩ := hq
        exact hp i hi
      simp [hp, hq]
    · have hq : Q h := by
        simp only [P, not_forall, not_ne_iff] at hp
        exact hp
      simp [hp, hq]
  have hzeroSum :
      (∑ h : Fin 4 → Fin (2 * H + 1),
        if ∀ i, hwCentered H (h i) = 0 then (2 * M + 1) ^ 4 else 0) =
          (2 * M + 1) ^ 4 := by
    let z : Fin (2 * H + 1) := ⟨H, by omega⟩
    have hall (h : Fin 4 → Fin (2 * H + 1)) :
        (∀ i, hwCentered H (h i) = 0) ↔ h = fun _ ↦ z := by
      constructor
      · intro hh
        funext i
        simpa [z] using (hw_centered_eq_zero_iff H (h i)).mp (hh i)
      · rintro rfl i
        simp [z, hwCentered]
    simp_rw [hall]
    simp
  have hhasZeroSum :
      (∑ h : Fin 4 → Fin (2 * H + 1),
        if Q h then (2 * M + 1) ^ 3 else 0) =
          #(hwHasZero H) * (2 * M + 1) ^ 3 := by
    change (∑ h : Fin 4 → Fin (2 * H + 1),
      if ∃ i, hwCentered H (h i) = 0 then (2 * M + 1) ^ 3 else 0) = _
    rw [← Finset.sum_filter]
    simp [hwHasZero]
  have hbad :
      (∑ h : Fin 4 → Fin (2 * H + 1), if Q h then F h else 0) ≤
        (2 * M + 1) ^ 4 + #(hwHasZero H) * (2 * M + 1) ^ 3 := by
    calc
      (∑ h : Fin 4 → Fin (2 * H + 1), if Q h then F h else 0) ≤
          ∑ h : Fin 4 → Fin (2 * H + 1),
            ((if ∀ i, hwCentered H (h i) = 0 then (2 * M + 1) ^ 4 else 0) +
              if Q h then (2 * M + 1) ^ 3 else 0) := by
        apply Finset.sum_le_sum
        intro h _
        by_cases hq : Q h
        · rw [ite_eq_left hq, ite_eq_left hq]
          by_cases hall : ∀ i, hwCentered H (h i) = 0
          · rw [ite_eq_left hall]
            exact (Finset.card_le_univ _).trans (by simp)
          · rw [ite_eq_right hall, zero_add]
            simp only [not_forall] at hall
            obtain ⟨i, hi⟩ := hall
            exact hw_linearFiber_card_le M (fun i ↦ hwCentered H (h i)) hi
        · rw [ite_eq_right hq]
          omega
      _ = (2 * M + 1) ^ 4 + #(hwHasZero H) * (2 * M + 1) ^ 3 := by
        rw [Finset.sum_add_distrib, hzeroSum, hhasZeroSum]
  rw [hw_centeredFourTerm_card_eq_sum]
  calc
    (∑ h : Fin 4 → Fin (2 * H + 1), F h) =
        (∑ h : Fin 4 → Fin (2 * H + 1), if P h then F h else 0) +
          ∑ h : Fin 4 → Fin (2 * H + 1), if Q h then F h else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro h _
      exact hpart h
    _ ≤ #(hwCenteredFourNonzero H M) +
        ((2 * M + 1) ^ 4 + #(hwHasZero H) * (2 * M + 1) ^ 3) := by
      rw [hw_centeredFourNonzero_card_eq_sum]
      exact Nat.add_le_add le_rfl hbad
    _ ≤ hwFourTermCount H M + (2 * M + 1) ^ 4 +
        4 * (2 * H + 1) ^ 3 * (2 * M + 1) ^ 3 := by
      have hnonzero := hw_centeredFourNonzero_card_le H M
      have hzero := Nat.mul_le_mul_right ((2 * M + 1) ^ 3) (hw_hasZero_card_le H)
      omega

lemma hw_pairCount_zero_le (H M : ℕ) :
    hwPairCount H M 0 ≤ 4 * H ^ 2 * (2 * M + 1) := by
  rw [hw_pairCount_eq]
  calc
    (∑ h₁ : hwSigned H, ∑ h₂ : hwSigned H,
        #(hwPairFiber M (hwSignedVal H h₁) (hwSignedVal H h₂) 0)) ≤
        ∑ _h₁ : hwSigned H, ∑ _h₂ : hwSigned H, (2 * M + 1) := by
      gcongr with h₁ h₂
      exact hw_pairFiber_card_le_fin M (hw_signedVal_ne_zero H h₁)
    _ = 4 * H ^ 2 * (2 * M + 1) := by
      simp [hwSigned]
      ring

lemma hw_pairCount_real_le (H M : ℕ) (hHM : H ≤ M) {n : ℤ} (hn : n ≠ 0) :
    (hwPairCount H M n : ℝ) ≤
      32 * H * (M + 1) * hwSigmaInv n.natAbs := by
  have hnabs : n.natAbs ≠ 0 := (Int.natAbs_pos.mpr hn).ne'
  calc
    (hwPairCount H M n : ℝ) =
        ∑ h₁ : hwSigned H, ∑ h₂ : hwSigned H,
          (#(hwPairFiber M (hwSignedVal H h₁) (hwSignedVal H h₂) n) : ℝ) := by
      rw [hw_pairCount_eq]
      push_cast
      rfl
    _ ≤ ∑ h₁ : hwSigned H, ∑ h₂ : hwSigned H,
        4 * (M + 1) *
          (if (h₁.2.val + 1).gcd (h₂.2.val + 1) ∣ n.natAbs then
            ((h₁.2.val + 1).gcd (h₂.2.val + 1) : ℝ) /
              max (h₁.2.val + 1) (h₂.2.val + 1) else 0) := by
      gcongr with h₁ h₂
      exact hw_pairFiber_card_real_le H M hHM h₁ h₂ n
    _ = 4 * (M + 1) * (∑ h₁ : hwSigned H, ∑ h₂ : hwSigned H,
        if (h₁.2.val + 1).gcd (h₂.2.val + 1) ∣ n.natAbs then
          ((h₁.2.val + 1).gcd (h₂.2.val + 1) : ℝ) /
            max (h₁.2.val + 1) (h₂.2.val + 1) else 0) := by
      simp_rw [Finset.mul_sum]
    _ ≤ 4 * (M + 1) * (8 * H * hwSigmaInv n.natAbs) := by
      gcongr
      exact hw_sum_signed_gcd_inv_max_le H n.natAbs hnabs
    _ = 32 * H * (M + 1) * hwSigmaInv n.natAbs := by ring

lemma hw_fourTermCount_real_le (H M : ℕ) (hH : 0 < H) (hHM : H ≤ M) :
    (hwFourTermCount H M : ℝ) ≤
      (144 + 16384 * hwZetaTwo ^ 3) * (H * M) ^ 3 := by
  let B := 2 * H * M
  let T := Finset.Icc (-(B : ℤ)) (B : ℤ)
  have hM : 0 < M := hH.trans_le hHM
  have hcast : (hwFourTermCount H M : ℝ) =
      ∑ n ∈ T, (hwPairCount H M n : ℝ) * hwPairCount H M (-n) := by
    rw [hw_fourTermCount_eq]
    push_cast
    rfl
  have hz : {n ∈ T | n = 0} = {0} := by
    ext n
    simp only [mem_filter, mem_singleton, T, mem_Icc]
    constructor
    · exact fun h ↦ h.2
    · intro h
      subst n
      constructor <;> omega
  have hsplit :
      (∑ n ∈ T, (hwPairCount H M n : ℝ) * hwPairCount H M (-n)) =
        (hwPairCount H M 0 : ℝ) ^ 2 +
          ∑ n ∈ T with n ≠ 0,
            (hwPairCount H M n : ℝ) * hwPairCount H M (-n) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := T) (p := fun n ↦ n ≠ 0)]
    simp only [not_ne_iff]
    rw [hz]
    simp [add_comm, pow_two]
  have hzeroBase : (hwPairCount H M 0 : ℝ) ≤ 12 * H ^ 2 * M := by
    have hnat : 4 * H ^ 2 * (2 * M + 1) ≤ 12 * H ^ 2 * M := by
      calc
        4 * H ^ 2 * (2 * M + 1) ≤ 4 * H ^ 2 * (3 * M) := by
          gcongr
          omega
        _ = 12 * H ^ 2 * M := by ring
    exact_mod_cast (hw_pairCount_zero_le H M).trans hnat
  have hzero : (hwPairCount H M 0 : ℝ) ^ 2 ≤ 144 * (H * M) ^ 3 := by
    calc
      (hwPairCount H M 0 : ℝ) ^ 2 ≤ (12 * H ^ 2 * M : ℝ) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) hzeroBase 2
      _ = (144 * (H : ℝ) ^ 3 * M ^ 2) * H := by ring
      _ ≤ (144 * (H : ℝ) ^ 3 * M ^ 2) * M := by
        gcongr
      _ = 144 * (H * M) ^ 3 := by ring
  have hpair (n : ℤ) (hn : n ≠ 0) :
      (hwPairCount H M n : ℝ) ≤
        64 * H * M * hwSigmaInv n.natAbs := by
    calc
      (hwPairCount H M n : ℝ) ≤
          32 * H * (M + 1) * hwSigmaInv n.natAbs :=
        hw_pairCount_real_le H M hHM hn
      _ ≤ 32 * H * (2 * M) * hwSigmaInv n.natAbs := by
        apply mul_le_mul_of_nonneg_right _ (hw_sigmaInv_nonneg n.natAbs)
        gcongr
        exact_mod_cast (by omega : M + 1 ≤ 2 * M)
      _ = 64 * H * M * hwSigmaInv n.natAbs := by ring
  have hpoint (n : ℤ) (hn : n ≠ 0) :
      (hwPairCount H M n : ℝ) * hwPairCount H M (-n) ≤
        4096 * H ^ 2 * M ^ 2 * hwSigmaInv n.natAbs ^ 2 := by
    have hnneg : -n ≠ 0 := by simpa using hn
    have h₁ := hpair n hn
    have h₂ := hpair (-n) hnneg
    rw [Int.natAbs_neg] at h₂
    calc
      (hwPairCount H M n : ℝ) * hwPairCount H M (-n) ≤
          (64 * H * M * hwSigmaInv n.natAbs) *
            (64 * H * M * hwSigmaInv n.natAbs) := by
        exact mul_le_mul h₁ h₂ (by positivity)
          (mul_nonneg (by positivity) (hw_sigmaInv_nonneg n.natAbs))
      _ = 4096 * H ^ 2 * M ^ 2 * hwSigmaInv n.natAbs ^ 2 := by ring
  have hnonzero :
      (∑ n ∈ T with n ≠ 0,
        (hwPairCount H M n : ℝ) * hwPairCount H M (-n)) ≤
          16384 * (H * M) ^ 3 * hwZetaTwo ^ 3 := by
    calc
      (∑ n ∈ T with n ≠ 0,
        (hwPairCount H M n : ℝ) * hwPairCount H M (-n)) ≤
          ∑ n ∈ T with n ≠ 0,
            4096 * H ^ 2 * M ^ 2 * hwSigmaInv n.natAbs ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact hpoint n (mem_filter.mp hn).2
      _ = 4096 * H ^ 2 * M ^ 2 *
          (∑ n ∈ T with n ≠ 0, hwSigmaInv n.natAbs ^ 2) := by
        rw [Finset.mul_sum]
      _ ≤ 4096 * H ^ 2 * M ^ 2 *
          (2 * ∑ a ∈ Finset.Icc 1 B, hwSigmaInv a ^ 2) := by
        gcongr
        simpa [T] using hw_sum_int_natAbs_le B (fun a ↦ hwSigmaInv a ^ 2)
          (fun a ↦ sq_nonneg _)
      _ ≤ 4096 * H ^ 2 * M ^ 2 * (2 * (B * hwZetaTwo ^ 3)) := by
        gcongr
        exact hw_sigmaInv_sq_sum_le B
      _ = 16384 * (H * M) ^ 3 * hwZetaTwo ^ 3 := by
        dsimp [B]
        push_cast
        ring
  rw [hcast, hsplit]
  calc
    (hwPairCount H M 0 : ℝ) ^ 2 +
        ∑ n ∈ T with n ≠ 0,
          (hwPairCount H M n : ℝ) * hwPairCount H M (-n) ≤
      144 * (H * M) ^ 3 + 16384 * (H * M) ^ 3 * hwZetaTwo ^ 3 :=
        add_le_add hzero hnonzero
    _ = (144 + 16384 * hwZetaTwo ^ 3) * (H * M) ^ 3 := by ring

lemma hw_exists_fourTermCount_bound :
    ∃ C : ℕ, 0 < C ∧ ∀ H M : ℕ, 0 < H → H ≤ M →
      hwFourTermCount H M ≤ C * (H * M) ^ 3 := by
  let R : ℝ := 144 + 16384 * hwZetaTwo ^ 3
  let C := ⌈R⌉₊
  have hR : 0 < R := by
    dsimp [R]
    have hz3 : 0 ≤ hwZetaTwo ^ 3 := pow_nonneg hw_zetaTwo_nonneg 3
    nlinarith
  refine ⟨C, Nat.ceil_pos.mpr hR, ?_⟩
  intro H M hH hHM
  have hmain := hw_fourTermCount_real_le H M hH hHM
  have hceil : R ≤ (C : ℝ) := Nat.le_ceil R
  have hpow : (0 : ℝ) ≤ (H * M : ℕ) ^ 3 := by positivity
  have hbound : (hwFourTermCount H M : ℝ) ≤ (C : ℝ) * ((H * M : ℕ) : ℝ) ^ 3 := by
    calc
      (hwFourTermCount H M : ℝ) ≤ R * ((H * M : ℕ) : ℝ) ^ 3 := by
        simpa [R] using hmain
      _ ≤ (C : ℝ) * ((H * M : ℕ) : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right hceil hpow
  exact_mod_cast hbound

end MathlibExt.NumberTheory.HilbertWaringWanted
