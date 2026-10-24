/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HilbertWaring.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

import sympy.atlas.Combinatorics.Schnirelmann
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

/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/

namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset
open scoped Pointwise

private def hwCentered (M : ℕ) (x : Fin (2 * M + 1)) : ℤ :=
  x.val - M

private def hwToCentered (M : ℕ) (z : ℤ) (hz : z.natAbs ≤ M) : Fin (2 * M + 1) :=
  ⟨(z + M).toNat, by
    have hzle : z ≤ (z.natAbs : ℤ) := Int.le_natAbs
    have hnzle : -z ≤ ((-z).natAbs : ℤ) := Int.le_natAbs
    rw [Int.natAbs_neg] at hnzle
    have habs : (z.natAbs : ℤ) ≤ M := by exact_mod_cast hz
    have hlo : -(M : ℤ) ≤ z := by omega
    have hhi : z ≤ M := by omega
    have hz0 : 0 ≤ z + M := by omega
    have hz2 : z + M < 2 * M + 1 := by omega
    exact (Int.toNat_lt hz0).2 hz2⟩

private def hwPairFiber (M : ℕ) (h₁ h₂ n : ℤ) :
    Finset (Fin (2 * M + 1) × Fin (2 * M + 1)) :=
  Finset.univ.filter fun x ↦
    h₁ * hwCentered M x.1 + h₂ * hwCentered M x.2 = n

private noncomputable def hwSigmaInv (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (d : ℝ)⁻¹

private noncomputable def hwZetaTwo : ℝ :=
  ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹

private abbrev hwSigned (H : ℕ) := Fin 2 × Fin H

private def hwSignedVal (H : ℕ) (h : hwSigned H) : ℤ :=
  if h.1 = 0 then (h.2.val + 1 : ℕ) else -((h.2.val + 1 : ℕ) : ℤ)

@[simp] private lemma hw_signedVal_natAbs (H : ℕ) (h : hwSigned H) :
    (hwSignedVal H h).natAbs = h.2.val + 1 := by
  rcases h with ⟨s, i⟩
  fin_cases s
  · change (((i.val + 1 : ℕ) : ℤ)).natAbs = i.val + 1
    exact Int.natAbs_natCast _
  · change (-((i.val + 1 : ℕ) : ℤ)).natAbs = i.val + 1
    rw [Int.natAbs_neg]
    exact Int.natAbs_natCast _

private lemma hw_signedVal_ne_zero (H : ℕ) (h : hwSigned H) : hwSignedVal H h ≠ 0 := by
  apply Int.natAbs_pos.mp
  rw [hw_signedVal_natAbs]
  omega

private def hwSignedToCentered (H : ℕ) (h : hwSigned H) : Fin (2 * H + 1) :=
  if h.1 = 0 then
    ⟨H + (h.2.val + 1), by omega⟩
  else
    ⟨H - (h.2.val + 1), by omega⟩

private lemma hw_centered_signedToCentered (H : ℕ) (h : hwSigned H) :
    hwCentered H (hwSignedToCentered H h) = hwSignedVal H h := by
  rcases h with ⟨s, i⟩
  fin_cases s <;> simp [hwSignedToCentered, hwSignedVal, hwCentered]

private def hwCenteredToSigned
    (H : ℕ) (x : {x : Fin (2 * H + 1) // hwCentered H x ≠ 0}) : hwSigned H :=
  if hx : H < x.1.val then
    (0, ⟨x.1.val - H - 1, by omega⟩)
  else
    (1, ⟨H - x.1.val - 1, by
      have hne : x.1.val ≠ H := by
        intro h
        apply x.2
        simp [hwCentered, h]
      omega⟩)

private def hwSignedEquivCentered (H : ℕ) :
    hwSigned H ≃ {x : Fin (2 * H + 1) // hwCentered H x ≠ 0} where
  toFun h := ⟨hwSignedToCentered H h, by
    rw [hw_centered_signedToCentered]
    exact hw_signedVal_ne_zero H h⟩
  invFun := hwCenteredToSigned H
  left_inv h := by
    rcases h with ⟨s, i⟩
    fin_cases s
    · apply Prod.ext
      · apply Fin.ext
        simp [hwCenteredToSigned, hwSignedToCentered]
      · apply Fin.ext
        simp [hwCenteredToSigned, hwSignedToCentered]
    · have hi := i.isLt
      have hnot : ¬H < H - (i.val + 1) := by omega
      apply Prod.ext
      · apply Fin.ext
        simp [hwCenteredToSigned, hwSignedToCentered, hnot]
      · apply Fin.ext
        simp [hwCenteredToSigned, hwSignedToCentered, hnot]
        omega
  right_inv x := by
    apply Subtype.ext
    apply Fin.ext
    by_cases hx : H < x.1.val
    · simp [hwCenteredToSigned, hwSignedToCentered, hx]
      omega
    · have hne : x.1.val ≠ H := by
        intro h
        apply x.2
        simp [hwCentered, h]
      simp [hwCenteredToSigned, hwSignedToCentered, hx]
      omega

private def hwLinearFiber (M : ℕ) (c : Fin 4 → ℤ) :
    Finset (Fin 4 → Fin (2 * M + 1)) :=
  Finset.univ.filter fun m ↦ ∑ i, c i * hwCentered M (m i) = 0

private def hwCoordZero (H : ℕ) (i : Fin 4) :
    Finset (Fin 4 → Fin (2 * H + 1)) :=
  Finset.univ.filter fun h ↦ hwCentered H (h i) = 0

private def hwHasZero (H : ℕ) : Finset (Fin 4 → Fin (2 * H + 1)) :=
  Finset.univ.filter fun h ↦ ∃ i, hwCentered H (h i) = 0

private lemma hw_pairFiber_card_real_le (H M : ℕ) (hHM : H ≤ M)
    (h₁ h₂ : hwSigned H) (n : ℤ) :
    (#(hwPairFiber M (hwSignedVal H h₁) (hwSignedVal H h₂) n) : ℝ) ≤
      4 * (M + 1) *
        (if (h₁.2.val + 1).gcd (h₂.2.val + 1) ∣ n.natAbs then
          ((h₁.2.val + 1).gcd (h₂.2.val + 1) : ℝ) /
            max (h₁.2.val + 1) (h₂.2.val + 1) else 0) := by
  let a := hwSignedVal H h₁
  let b := hwSignedVal H h₂
  have ha0 : a ≠ 0 := hw_signedVal_ne_zero H h₁
  have hb0 : b ≠ 0 := hw_signedVal_ne_zero H h₂
  have haM : a.natAbs ≤ M := (hw_signedVal_natAbs_le H h₁).trans hHM
  have hbM : b.natAbs ≤ M := (hw_signedVal_natAbs_le H h₂).trans hHM
  have hgcd : a.gcd b = (h₁.2.val + 1).gcd (h₂.2.val + 1) := by
    simp [a, b, Int.gcd_eq_natAbs]
  split_ifs with hdvd
  · have hmax0 : (0 : ℝ) < max a.natAbs b.natAbs := by positivity
    have hmax : max a.natAbs b.natAbs =
        max (h₁.2.val + 1) (h₂.2.val + 1) := by simp [a, b]
    rw [← hgcd, ← hmax]
    rw [show (4 : ℝ) * (M + 1) * ((a.gcd b : ℝ) / max a.natAbs b.natAbs) =
        (4 * (M + 1) * (a.gcd b : ℝ)) / max a.natAbs b.natAbs by ring]
    rw [le_div_iff₀ hmax0]
    exact_mod_cast hw_pairFiber_card_mul_max_le M ha0 hb0 haM hbM
  · have hempty : hwPairFiber M a b n = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro p hp
      apply hdvd
      rw [← hgcd]
      exact hw_gcd_dvd_natAbs_of_pairFiber_nonempty M ⟨p, hp⟩
    have hempty' : hwPairFiber M (hwSignedVal H h₁) (hwSignedVal H h₂) n = ∅ := by
      simpa [a, b] using hempty
    simp [hempty']

private abbrev hwPairData (H M : ℕ) :=
  (hwSigned H × hwSigned H) × (Fin (2 * M + 1) × Fin (2 * M + 1))

private def hwPairVal (H M : ℕ) (p : hwPairData H M) : ℤ :=
  hwSignedVal H p.1.1 * hwCentered M p.2.1 +
    hwSignedVal H p.1.2 * hwCentered M p.2.2

private def hwPairCount (H M : ℕ) (n : ℤ) : ℕ :=
  #((Finset.univ : Finset (hwPairData H M)).filter fun p ↦ hwPairVal H M p = n)

private def hwFourTermCount (H M : ℕ) : ℕ :=
  #((Finset.univ : Finset (hwPairData H M × hwPairData H M)).filter fun p ↦
    hwPairVal H M p.1 + hwPairVal H M p.2 = 0)

private def hwCenteredFourTerm (H M : ℕ) :
    Finset ((Fin 4 → Fin (2 * H + 1)) × (Fin 4 → Fin (2 * M + 1))) :=
  Finset.univ.filter fun p ↦
    ∑ i, hwCentered H (p.1 i) * hwCentered M (p.2 i) = 0

private def hwCenteredFourNonzero (H M : ℕ) :
    Finset ((Fin 4 → Fin (2 * H + 1)) × (Fin 4 → Fin (2 * M + 1))) :=
  Finset.univ.filter fun p ↦
    (∑ i, hwCentered H (p.1 i) * hwCentered M (p.2 i) = 0) ∧
      ∀ i, hwCentered H (p.1 i) ≠ 0

private def hwPackCenteredNonzero (H M : ℕ)
    (p : {p // p ∈ hwCenteredFourNonzero H M}) :
    hwPairData H M × hwPairData H M :=
  let s : Fin 4 → hwSigned H := fun i ↦
    (hwSignedEquivCentered H).symm
      ⟨p.1.1 i, (Finset.mem_filter.mp p.2).2.2 i⟩
  (((s 0, s 1), (p.1.2 0, p.1.2 1)),
    ((s 2, s 3), (p.1.2 2, p.1.2 3)))

private lemma hw_packCenteredNonzero_mem (H M : ℕ)
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

private lemma hw_centeredFourNonzero_card_le (H M : ℕ) :
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

private lemma hw_centeredFourTerm_card_le (H M : ℕ) :
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

private lemma hw_pairCount_zero_le (H M : ℕ) :
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

private lemma hw_pairCount_real_le (H M : ℕ) (hHM : H ≤ M) {n : ℤ} (hn : n ≠ 0) :
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

private lemma hw_fourTermCount_real_le (H M : ℕ) (hH : 0 < H) (hHM : H ≤ M) :
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

private lemma hw_exists_fourTermCount_bound :
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

private def hwTupleSum (r N : ℕ) (f : ℕ → ℤ) (x : Fin r → Fin (N + 1)) : ℤ :=
  ∑ i, f (x i)

private noncomputable def hwWeylSum (P N : ℕ) [NeZero P]
    (f : ℕ → ℤ) (a : ZMod P) : ℂ :=
  ∑ n : Fin (N + 1), ZMod.stdAddChar (a * (f n : ZMod P))

private def hwMomentFinset (r N : ℕ) (f : ℕ → ℤ) :
    Finset ((Fin r → Fin (N + 1)) × (Fin r → Fin (N + 1))) :=
  Finset.univ.filter fun xy ↦ hwTupleSum r N f xy.1 = hwTupleSum r N f xy.2

private def hwFinLift {A B : ℕ} (hAB : A ≤ B) (x : Fin (A + 1)) : Fin (B + 1) :=
  ⟨x.val, by omega⟩

private def hwMomentLift (r A B : ℕ) (hAB : A ≤ B) :
    ((Fin r → Fin (A + 1)) × (Fin r → Fin (A + 1))) →
      ((Fin r → Fin (B + 1)) × (Fin r → Fin (B + 1))) :=
  fun p ↦ (fun i ↦ hwFinLift hAB (p.1 i), fun i ↦ hwFinLift hAB (p.2 i))

private def hwTupleImage (r N : ℕ) (f : ℕ → ℤ) : Finset ℤ :=
  (Finset.univ : Finset (Fin r → Fin (N + 1))).image (hwTupleSum r N f)

private def hwValueFiber (r N : ℕ) (f : ℕ → ℤ) (t : ℤ) :
    Finset (Fin r → Fin (N + 1)) :=
  Finset.univ.filter fun x ↦ hwTupleSum r N f x = t

private def hwDiffFiber (r N : ℕ) (f : ℕ → ℤ) (m : ℤ) :
    Finset ((Fin r → Fin (N + 1)) × (Fin r → Fin (N + 1))) :=
  Finset.univ.filter fun p ↦ hwTupleSum r N f p.1 - hwTupleSum r N f p.2 = m

private def hwSumFiber (r N : ℕ) (f : ℕ → ℤ) (m : ℤ) :
    Finset ((Fin r → Fin (N + 1)) × (Fin r → Fin (N + 1))) :=
  Finset.univ.filter fun p ↦ hwTupleSum r N f p.1 + hwTupleSum r N f p.2 = m

private def hwPolyEval (k : ℕ) (a : Fin (k + 1) → ℤ) (n : ℕ) : ℤ :=
  ∑ j, a j * (n : ℤ) ^ j.val

private def hwCoeffBound (k c N : ℕ) (a : Fin (k + 1) → ℤ) : Prop :=
  ∀ j, (a j).natAbs ≤ c * N ^ (k - j.val)

private lemma hw_fin_sub_natAbs_le (N : ℕ) (x y : Fin (N + 1)) :
    ((x.val : ℤ) - y.val).natAbs ≤ N := by
  by_cases hxy : x.val ≤ y.val
  · rw [Int.natAbs_natCast_sub_natCast_of_le hxy]
    have hy := y.isLt
    omega
  · rw [Int.natAbs_natCast_sub_natCast_of_ge (Nat.le_of_not_ge hxy)]
    have hx := x.isLt
    omega

private lemma hw_quadratic_linear_natAbs_le (c N : ℕ) (a : Fin 3 → ℤ)
    (ha : hwCoeffBound 2 c N a) (x y : Fin (N + 1)) :
    (a 2 * ((x.val : ℤ) + y.val) + a 1).natAbs ≤ 3 * c * N := by
  have ha₂ : (a 2).natAbs ≤ c := by
    simpa [hwCoeffBound] using ha (2 : Fin 3)
  have ha₁ : (a 1).natAbs ≤ c * N := by
    simpa [hwCoeffBound] using ha (1 : Fin 3)
  have hxy : (((x.val : ℤ) + y.val).natAbs) ≤ 2 * N := by
    rw [show (x.val : ℤ) + y.val = ((x.val + y.val : ℕ) : ℤ) by norm_num,
      Int.natAbs_natCast]
    omega
  calc
    (a 2 * ((x.val : ℤ) + y.val) + a 1).natAbs ≤
        (a 2 * ((x.val : ℤ) + y.val)).natAbs + (a 1).natAbs :=
      Int.natAbs_add_le _ _
    _ = (a 2).natAbs * ((x.val : ℤ) + y.val).natAbs + (a 1).natAbs := by
      rw [Int.natAbs_mul]
    _ ≤ c * (2 * N) + c * N := Nat.add_le_add (Nat.mul_le_mul ha₂ hxy) ha₁
    _ = 3 * c * N := by ring

private def hwQuadraticMap (c N : ℕ) (a : Fin 3 → ℤ)
    (ha : hwCoeffBound 2 c N a)
    (p : {p // p ∈ hwMomentFinset 4 N (hwPolyEval 2 a)}) :
    (Fin 4 → Fin (2 * N + 1)) × (Fin 4 → Fin (2 * (3 * c * N) + 1)) :=
  (fun i ↦ hwToCentered N ((p.1.1 i).val - (p.1.2 i).val)
      (hw_fin_sub_natAbs_le N (p.1.1 i) (p.1.2 i)),
    fun i ↦ hwToCentered (3 * c * N)
      (a 2 * ((p.1.1 i).val + (p.1.2 i).val) + a 1)
      (hw_quadratic_linear_natAbs_le c N a ha (p.1.1 i) (p.1.2 i)))

private lemma hw_quadratic_moment_bound (c : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (N : ℕ) (a : Fin 3 → ℤ), 0 < N →
      hwCoeffBound 2 c N a → a 2 ≠ 0 →
        #(hwMomentFinset 4 N (hwPolyEval 2 a)) ≤ C * N ^ 6 := by
  obtain ⟨C₀, hC₀, hfour⟩ := hw_exists_fourTermCount_bound
  let D := 3 * c
  let E := 2 * D + 1
  let C := C₀ * D ^ 3 + E ^ 4 + 108 * E ^ 3
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N a hN ha ha₂
  have hc : 0 < c := by
    have hbound := ha (2 : Fin 3)
    have hpos := Int.natAbs_pos.mpr ha₂
    norm_num at hbound
    omega
  have hD : 0 < D := by dsimp [D]; positivity
  have hNM : N ≤ D * N := by
    apply Nat.le_mul_of_pos_left
    exact hD
  have htwoN : 2 * N + 1 ≤ 3 * N := by omega
  have htwoM : 2 * (D * N) + 1 ≤ E * N := by
    rw [show E * N = 2 * (D * N) + N by dsimp [E]; ring]
    omega
  have hfour' : hwFourTermCount N (D * N) ≤ C₀ * D ^ 3 * N ^ 6 := by
    calc
      hwFourTermCount N (D * N) ≤ C₀ * (N * (D * N)) ^ 3 :=
        hfour N (D * N) hN hNM
      _ = C₀ * D ^ 3 * N ^ 6 := by ring
  have hquartic : (2 * (D * N) + 1) ^ 4 ≤ E ^ 4 * N ^ 6 := by
    calc
      (2 * (D * N) + 1) ^ 4 ≤ (E * N) ^ 4 := Nat.pow_le_pow_left htwoM 4
      _ = E ^ 4 * N ^ 4 := by ring
      _ ≤ E ^ 4 * N ^ 6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN (by omega))
  have hcubic : 4 * (2 * N + 1) ^ 3 * (2 * (D * N) + 1) ^ 3 ≤
      108 * E ^ 3 * N ^ 6 := by
    calc
      4 * (2 * N + 1) ^ 3 * (2 * (D * N) + 1) ^ 3 ≤
          4 * (3 * N) ^ 3 * (E * N) ^ 3 := by
        gcongr
      _ = 108 * E ^ 3 * N ^ 6 := by ring
  have hcenter := hw_centeredFourTerm_card_le N (D * N)
  have hcenter' : #(hwCenteredFourTerm N (D * N)) ≤ C * N ^ 6 := by
    calc
      #(hwCenteredFourTerm N (D * N)) ≤
          hwFourTermCount N (D * N) + (2 * (D * N) + 1) ^ 4 +
            4 * (2 * N + 1) ^ 3 * (2 * (D * N) + 1) ^ 3 := hcenter
      _ ≤ C₀ * D ^ 3 * N ^ 6 + E ^ 4 * N ^ 6 + 108 * E ^ 3 * N ^ 6 :=
        Nat.add_le_add (Nat.add_le_add hfour' hquartic) hcubic
      _ = C * N ^ 6 := by dsimp [C]; ring
  calc
    #(hwMomentFinset 4 N (hwPolyEval 2 a)) ≤
        #(hwCenteredFourTerm N (3 * c * N)) :=
      hw_quadratic_moment_le_centered c N a ha ha₂
    _ = #(hwCenteredFourTerm N (D * N)) := by rfl
    _ ≤ C * N ^ 6 := hcenter'

private def hwDiffCoeff (k : ℕ) (a : Fin (k + 1) → ℤ) (h : ℕ) : Fin k → ℤ :=
  fun i ↦ ∑ j : Fin (k + 1), if i.val < j.val then
    a j * (j.val.choose i.val : ℤ) * (h : ℤ) ^ (j.val - i.val - 1) else 0

private def hwDiffCoeffs (k : ℕ) (hk : 0 < k) (a : Fin (k + 1) → ℤ) (h : ℕ) :
    Fin (k - 1 + 1) → ℤ :=
  fun i ↦ hwDiffCoeff k a h ⟨i.val, by omega⟩

private abbrev hwOffDiag (N : ℕ) :=
  {p : Fin (N + 1) × Fin (N + 1) // p.1 ≠ p.2}

private def hwPairSignedDiff (N : ℕ) (p : hwOffDiag N) : hwSigned N :=
  if hp : p.1.2 < p.1.1 then
    (0, ⟨p.1.1.val - p.1.2.val - 1, by
      have hx := p.1.1.isLt
      have hpv : p.1.2.val < p.1.1.val := hp
      omega⟩)
  else
    (1, ⟨p.1.2.val - p.1.1.val - 1, by
      have hy := p.1.2.isLt
      have hne := p.2
      omega⟩)

private def hwPairBase (N : ℕ) (p : hwOffDiag N) : Fin (N + 1) :=
  if p.1.2 < p.1.1 then p.1.2 else p.1.1

private def hwOffDiagFiber (N : ℕ) (h : hwSigned N) : Finset (hwOffDiag N) :=
  Finset.univ.filter fun p ↦ hwPairSignedDiff N p = h

private noncomputable def hwDiffBlock (P N : ℕ) [NeZero P] (f : ℕ → ℤ)
    (h : hwSigned N) (a : ZMod P) : ℂ :=
  ∑ p ∈ hwOffDiagFiber N h,
    ZMod.stdAddChar (a * ((f p.1.1 - f p.1.2 : ℤ) : ZMod P))

private def hwBlockLength (N : ℕ) (h : hwSigned N) : ℕ :=
  N - (h.2.val + 1)

private def hwPairOfBase (N : ℕ) (h : hwSigned N)
    (y : Fin (hwBlockLength N h + 1)) : hwOffDiag N :=
  if hs : h.1 = 0 then
    ⟨(⟨y.val + h.2.val + 1, by
        have hy := y.isLt
        dsimp [hwBlockLength] at hy
        omega⟩, ⟨y.val, by
        have hy := y.isLt
        dsimp [hwBlockLength] at hy
        omega⟩), by
      intro heq
      have heqval : y.val + h.2.val + 1 = y.val :=
        congrArg (fun z : Fin (N + 1) ↦ z.val) heq
      omega⟩
  else
    ⟨(⟨y.val, by
        have hy := y.isLt
        dsimp [hwBlockLength] at hy
        omega⟩, ⟨y.val + h.2.val + 1, by
        have hy := y.isLt
        dsimp [hwBlockLength] at hy
        omega⟩), by
      intro heq
      have heqval : y.val = y.val + h.2.val + 1 :=
        congrArg (fun z : Fin (N + 1) ↦ z.val) heq
      omega⟩

private abbrev hwBlockChoice (r N : ℕ) :=
  Σ h : hwSigned N,
    (Fin r → Fin (hwBlockLength N h + 1)) ×
      (Fin r → Fin (hwBlockLength N h + 1))

private def hwBlockChoiceDiff (k r N : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ) (z : hwBlockChoice r N) : ℤ :=
  hwTupleSum r (hwBlockLength N z.1)
      (hwPolyEval (k - 1) (hwDiffCoeffs k hk a (z.1.2.val + 1))) z.2.1 -
    hwTupleSum r (hwBlockLength N z.1)
      (hwPolyEval (k - 1) (hwDiffCoeffs k hk a (z.1.2.val + 1))) z.2.2

private def hwBlockChoiceFreq (k r N : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ) (z : hwBlockChoice r N) : ℤ :=
  hwSignedVal N z.1 * hwBlockChoiceDiff k r N hk a z

private def hwZeroQuadruples {C : Type*} [Fintype C] (v : C → ℤ) :
    Finset (Fin 4 → C) :=
  Finset.univ.filter fun u ↦ ∑ i, v (u i) = 0

private def hwBlockQuadMap (k r N M : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ)
    (hm : ∀ z : hwBlockChoice r N, (hwBlockChoiceDiff k r N hk a z).natAbs ≤ M)
    (u : Fin 4 → hwBlockChoice r N) :
    (Fin 4 → Fin (2 * N + 1)) × (Fin 4 → Fin (2 * M + 1)) :=
  (fun i ↦ hwSignedToCentered N (u i).1,
    fun i ↦ hwToCentered M (hwBlockChoiceDiff k r N hk a (u i)) (hm (u i)))

private lemma hw_blockQuadMap_mem (k r N M : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ)
    (hm : ∀ z : hwBlockChoice r N, (hwBlockChoiceDiff k r N hk a z).natAbs ≤ M)
    {u : Fin 4 → hwBlockChoice r N}
    (hu : u ∈ hwZeroQuadruples (hwBlockChoiceFreq k r N hk a)) :
    hwBlockQuadMap k r N M hk a hm u ∈ hwCenteredFourNonzero N M := by
  have hzero : ∑ i, hwBlockChoiceFreq k r N hk a (u i) = 0 :=
    (Finset.mem_filter.mp hu).2
  simp only [hwCenteredFourNonzero, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · simp only [hwBlockQuadMap, hw_centered_signedToCentered, hw_centered_toCentered]
    simpa [hwBlockChoiceFreq] using hzero
  · intro i
    simp only [hwBlockQuadMap, hw_centered_signedToCentered]
    exact hw_signedVal_ne_zero N (u i).1

private lemma hw_blockQuadMap_image_card_le (k r N M : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ)
    (hm : ∀ z : hwBlockChoice r N, (hwBlockChoiceDiff k r N hk a z).natAbs ≤ M) :
    #((hwZeroQuadruples (hwBlockChoiceFreq k r N hk a)).image
        (hwBlockQuadMap k r N M hk a hm)) ≤ hwFourTermCount N M := by
  calc
    #((hwZeroQuadruples (hwBlockChoiceFreq k r N hk a)).image
        (hwBlockQuadMap k r N M hk a hm)) ≤ #(hwCenteredFourNonzero N M) := by
      apply Finset.card_le_card
      intro b hb
      rcases Finset.mem_image.mp hb with ⟨u, hu, rfl⟩
      exact hw_blockQuadMap_mem k r N M hk a hm hu
    _ ≤ hwFourTermCount N M := hw_centeredFourNonzero_card_le N M

private def hwBlockChoiceEmbed (r N : ℕ) (z : hwBlockChoice r N) :
    hwSigned N ×
      ((Fin r → Fin (N + 1)) × (Fin r → Fin (N + 1))) :=
  (z.1, hwMomentLift r (hwBlockLength N z.1) N (Nat.sub_le _ _) z.2)

private lemma hw_zeroQuadruples_card_le (k r N M A : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ)
    (hm : ∀ z : hwBlockChoice r N, (hwBlockChoiceDiff k r N hk a z).natAbs ≤ M)
    (hA : ∀ h : hwSigned N,
      #(hwMomentFinset r N
        (hwPolyEval (k - 1) (hwDiffCoeffs k hk a (h.2.val + 1)))) ≤ A) :
    #(hwZeroQuadruples (hwBlockChoiceFreq k r N hk a)) ≤
      hwFourTermCount N M * A ^ 4 := by
  let S := hwZeroQuadruples (hwBlockChoiceFreq k r N hk a)
  let f := hwBlockQuadMap k r N M hk a hm
  have hmap : Set.MapsTo f (↑S) (↑(S.image f)) := by
    intro u hu
    exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  change #S ≤ _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    (∑ b ∈ S.image f, #{u ∈ S | f u = b}) ≤
        ∑ _b ∈ S.image f, A ^ 4 := by
      gcongr with b
      exact hw_blockQuadMap_fiber_card_le k r N M A hk a hm hA b
    _ = #(S.image f) * A ^ 4 := by simp
    _ ≤ hwFourTermCount N M * A ^ 4 := by
      gcongr
      exact hw_blockQuadMap_image_card_le k r N M hk a hm

private def hwStepR (k : ℕ) : ℕ := 4 * 8 ^ (k - 3)

private def hwStepD (k c : ℕ) : ℕ := (k + 1) * c * 2 ^ k

private def hwStepV (k c N : ℕ) : ℕ :=
  k * hwStepD k c * N ^ (k - 1)

private def hwStepM (k c N : ℕ) : ℕ :=
  max N (2 * hwStepR k * hwStepV k c N)

private def hwStepE (k c : ℕ) : ℕ :=
  2 * hwStepR k * k * hwStepD k c + 1

private lemma hw_step_zero_count_bound (k c Cᵢ C₄ N : ℕ) (hk : 3 ≤ k)
    (hN : 0 < N) (a : Fin (k + 1) → ℤ) (ha : hwCoeffBound k c N a)
    (haTop : a ⟨k, by omega⟩ ≠ 0)
    (hI : ∀ (N : ℕ) (b : Fin (k - 1 + 1) → ℤ), 0 < N →
      hwCoeffBound (k - 1) (hwStepD k c) N b → b ⟨k - 1, by omega⟩ ≠ 0 →
      #(hwMomentFinset (8 ^ (k - 2) / 2) N (hwPolyEval (k - 1) b)) ≤
        Cᵢ * N ^ (8 ^ (k - 2) - (k - 1)))
    (hfour : ∀ H M : ℕ, 0 < H → H ≤ M →
      hwFourTermCount H M ≤ C₄ * (H * M) ^ 3) :
    #(hwZeroQuadruples
        (hwBlockChoiceFreq k (hwStepR k) N (by omega) a)) ≤
      (C₄ * hwStepE k c ^ 3 * Cᵢ ^ 4) *
        N ^ (8 * hwStepR k - k + 4) := by
  let r := hwStepR k
  let D := hwStepD k c
  let V := hwStepV k c N
  let M := hwStepM k c N
  let A := Cᵢ * N ^ (2 * r - (k - 1))
  have hrel := hw_step_pow_relations k hk
  have hdegree := (hw_step_degree_bounds k hk).1
  have hm : ∀ z : hwBlockChoice r N,
      (hwBlockChoiceDiff k r N (by omega) a z).natAbs ≤ M := by
    intro z
    have hz := hw_blockChoiceDiff_natAbs_le k c r N (by omega) a ha z
    apply hz.trans
    change 2 * r * V ≤ M
    exact le_max_right _ _
  have hA : ∀ h : hwSigned N,
      #(hwMomentFinset r N
        (hwPolyEval (k - 1) (hwDiffCoeffs k (by omega) a (h.2.val + 1)))) ≤ A := by
    intro h
    have hh : h.2.val + 1 ≤ N := by omega
    have hcoeff : hwCoeffBound (k - 1) D N
        (hwDiffCoeffs k (by omega) a (h.2.val + 1)) := by
      simpa [D, hwStepD] using
        hw_diffCoeffs_bound k c N (h.2.val + 1) (by omega) hh a ha
    have htop : (hwDiffCoeffs k (by omega) a (h.2.val + 1)) ⟨k - 1, by omega⟩ =
        (k : ℤ) * a ⟨k, by omega⟩ := by
      simpa [hwDiffCoeffs] using
        hw_diffCoeff_top k (h.2.val + 1) (by omega) a
    have htopne : (hwDiffCoeffs k (by omega) a (h.2.val + 1))
        ⟨k - 1, by omega⟩ ≠ 0 := by
      rw [htop]
      exact mul_ne_zero (by exact_mod_cast (show k ≠ 0 by omega)) haTop
    have hi := hI N (hwDiffCoeffs k (by omega) a (h.2.val + 1)) hN hcoeff htopne
    change #(hwMomentFinset r N
      (hwPolyEval (k - 1) (hwDiffCoeffs k (by omega) a (h.2.val + 1)))) ≤ A
    dsimp [A, r]
    rw [hrel.2.2.2, ← hrel.1] at hi
    exact hi
  have hzero := hw_zeroQuadruples_card_le k r N M A (by omega) a hm hA
  have hM := hw_stepM_bounds k c N hk hN
  have hfour' : hwFourTermCount N M ≤
      C₄ * hwStepE k c ^ 3 * N ^ (3 * k) := by
    have hpow : N * N ^ (k - 1) = N ^ k := by
      calc
        N * N ^ (k - 1) = N ^ (k - 1) * N := by ac_rfl
        _ = N ^ ((k - 1) + 1) := (pow_succ N (k - 1)).symm
        _ = N ^ k := by
          congr 2
          all_goals omega
    have hNM : N * M ≤ hwStepE k c * N ^ k := by
      calc
        N * M ≤ N * (hwStepE k c * N ^ (k - 1)) :=
          Nat.mul_le_mul_left N hM.2
        _ = hwStepE k c * N ^ k := by
          rw [← hpow]
          ring
    calc
      hwFourTermCount N M ≤ C₄ * (N * M) ^ 3 := hfour N M hN hM.1
      _ ≤ C₄ * (hwStepE k c * N ^ k) ^ 3 := by gcongr
      _ = C₄ * hwStepE k c ^ 3 * N ^ (3 * k) := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm k 3]
        ring
  have hA₄ : A ^ 4 = Cᵢ ^ 4 * N ^ (4 * (2 * r - (k - 1))) := by
    dsimp [A]
    rw [mul_pow, ← pow_mul, Nat.mul_comm (2 * r - (k - 1)) 4]
  calc
    #(hwZeroQuadruples (hwBlockChoiceFreq k r N (by omega) a)) ≤
        hwFourTermCount N M * A ^ 4 := hzero
    _ = hwFourTermCount N M *
        (Cᵢ ^ 4 * N ^ (4 * (2 * r - (k - 1)))) := by rw [hA₄]
    _ ≤ (C₄ * hwStepE k c ^ 3 * N ^ (3 * k)) *
        (Cᵢ ^ 4 * N ^ (4 * (2 * r - (k - 1)))) := by
      exact Nat.mul_le_mul_right _ hfour'
    _ = (C₄ * hwStepE k c ^ 3 * Cᵢ ^ 4) *
        N ^ (3 * k + 4 * (2 * r - (k - 1))) := by
      rw [pow_add]
      ring
    _ = (C₄ * hwStepE k c ^ 3 * Cᵢ ^ 4) *
        N ^ (8 * r - k + 4) := by
      congr 2
      omega

private def hwStepK (k c Cᵢ C₄ : ℕ) : ℕ :=
  C₄ * hwStepE k c ^ 3 * Cᵢ ^ 4

private def hwStepC (k c Cᵢ C₄ : ℕ) : ℕ :=
  2 ^ (8 * hwStepR k) *
    (2 ^ (8 * hwStepR k) +
      2 ^ (8 * hwStepR k - 4) * hwStepK k c Cᵢ C₄)

private lemma hw_moment_induction_step (k c Cᵢ C₄ : ℕ) (hk : 3 ≤ k)
    (hI : ∀ (N : ℕ) (b : Fin (k - 1 + 1) → ℤ), 0 < N →
      hwCoeffBound (k - 1) (hwStepD k c) N b → b ⟨k - 1, by omega⟩ ≠ 0 →
      #(hwMomentFinset (8 ^ (k - 2) / 2) N (hwPolyEval (k - 1) b)) ≤
        Cᵢ * N ^ (8 ^ (k - 2) - (k - 1)))
    (hfour : ∀ H M : ℕ, 0 < H → H ≤ M →
      hwFourTermCount H M ≤ C₄ * (H * M) ^ 3) :
    ∀ (N : ℕ) (a : Fin (k + 1) → ℤ), 0 < N →
      hwCoeffBound k c N a → a ⟨k, by omega⟩ ≠ 0 →
      #(hwMomentFinset (8 ^ (k - 1) / 2) N (hwPolyEval k a)) ≤
        hwStepC k c Cᵢ C₄ * N ^ (8 ^ (k - 1) - k) := by
  intro N a hN ha haTop
  let r := hwStepR k
  let M := hwStepM k c N
  let Vₑ := (k + 1) * c * N ^ k
  let P := max (2 * (8 * r) * Vₑ) (4 * N * M) + 1
  let K := hwStepK k c Cᵢ C₄
  let C := hwStepC k c Cᵢ C₄
  let _ : NeZero P := ⟨by simp [P]⟩
  have hrel := hw_step_pow_relations k hk
  have hdegrees := hw_step_degree_bounds k hk
  have hr : 0 < r := by
    exact Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have hm : ∀ z : hwBlockChoice r N,
      (hwBlockChoiceDiff k r N (by omega) a z).natAbs ≤ M := by
    intro z
    have hz := hw_blockChoiceDiff_natAbs_le k c r N (by omega) a ha z
    apply hz.trans
    change 2 * r * hwStepV k c N ≤ M
    exact le_max_right _ _
  have hf : ∀ n ≤ N, (hwPolyEval k a n).natAbs ≤ Vₑ := by
    intro n hn
    simpa [Vₑ, mul_assoc] using hw_polyEval_natAbs_le k c N n hn a ha
  have hPmoment : 2 * (8 * r) * Vₑ < P := by
    dsimp [P]
    exact (le_max_left _ _).trans_lt (Nat.lt_succ_self _)
  have hPblock : 4 * N * M < P := by
    dsimp [P]
    exact (le_max_right _ _).trans_lt (Nat.lt_succ_self _)
  have hmoment := hw_real_character_moment_eq_card_of_lt
    P (8 * r) N Vₑ (hwPolyEval k a) hf hPmoment
  have hblock := hw_block_fourth_sum_eq_zero_count_of_lt
    P k r N M (by omega) a hm hPblock
  have hzero := hw_step_zero_count_bound k c Cᵢ C₄ N hk hN a ha haTop hI hfour
  have hpoint :
      (∑ α : ZMod P, ‖hwWeylSum P N (hwPolyEval k a) α‖ ^ (16 * r)) ≤
        ∑ α : ZMod P, 2 ^ (8 * r) *
          (((N + 1 : ℕ) : ℝ) ^ (8 * r) +
            ((2 * N : ℕ) : ℝ) ^ (8 * r - 4) *
              (∑ h : hwSigned N,
                ‖hwDiffBlock P N (hwPolyEval k a) h α‖ ^ (2 * r)) ^ 4) := by
    apply Finset.sum_le_sum
    intro α _
    exact hw_weyl_pointwise_le P k r N hr a α
  have hsum :
      (∑ α : ZMod P, 2 ^ (8 * r) *
        (((N + 1 : ℕ) : ℝ) ^ (8 * r) +
          ((2 * N : ℕ) : ℝ) ^ (8 * r - 4) *
            (∑ h : hwSigned N,
              ‖hwDiffBlock P N (hwPolyEval k a) h α‖ ^ (2 * r)) ^ 4)) =
        (P : ℝ) * 2 ^ (8 * r) *
          (((N + 1 : ℕ) : ℝ) ^ (8 * r) +
            ((2 * N : ℕ) : ℝ) ^ (8 * r - 4) *
              #(hwZeroQuadruples
                (hwBlockChoiceFreq k r N (by omega) a))) := by
    calc
      _ = (∑ _α : ZMod P,
            (2 ^ (8 * r) : ℝ) * (((N + 1 : ℕ) : ℝ) ^ (8 * r)) +
          ∑ α : ZMod P,
            (2 ^ (8 * r) : ℝ) * (((2 * N : ℕ) : ℝ) ^ (8 * r - 4)) *
              (∑ h : hwSigned N,
                ‖hwDiffBlock P N (hwPolyEval k a) h α‖ ^ (2 * r)) ^ 4) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro α _
        push_cast
        ring
      _ = (P : ℝ) * ((2 ^ (8 * r) : ℝ) * (((N + 1 : ℕ) : ℝ) ^ (8 * r))) +
          ((2 ^ (8 * r) : ℝ) * (((2 * N : ℕ) : ℝ) ^ (8 * r - 4))) *
            ∑ α : ZMod P, (∑ h : hwSigned N,
              ‖hwDiffBlock P N (hwPolyEval k a) h α‖ ^ (2 * r)) ^ 4 := by
        rw [Finset.mul_sum]
        simp [ZMod.card]
      _ = _ := by
        rw [hblock]
        push_cast
        ring
  have hdiag : (((N + 1 : ℕ) : ℝ) ^ (8 * r)) ≤
      2 ^ (8 * r) * (N : ℝ) ^ (16 * r - k) := by
    have hNtwo : N + 1 ≤ 2 * N := by omega
    have hexp : 8 * r ≤ 16 * r - k := by omega
    calc
      (((N + 1 : ℕ) : ℝ) ^ (8 * r)) ≤
          (((2 * N : ℕ) : ℝ) ^ (8 * r)) := by
        exact_mod_cast (Nat.pow_le_pow_left hNtwo (8 * r))
      _ = 2 ^ (8 * r) * (N : ℝ) ^ (8 * r) := by
        push_cast
        rw [mul_pow]
      _ ≤ 2 ^ (8 * r) * (N : ℝ) ^ (16 * r - k) := by
        have hpN : N ^ (8 * r) ≤ N ^ (16 * r - k) :=
          Nat.pow_le_pow_right hN hexp
        apply mul_le_mul_of_nonneg_left
        · exact_mod_cast hpN
        · positivity
  have hblockNat :
      (2 * N) ^ (8 * r - 4) *
          #(hwZeroQuadruples (hwBlockChoiceFreq k r N (by omega) a)) ≤
        2 ^ (8 * r - 4) * K * N ^ (16 * r - k) := by
    calc
      (2 * N) ^ (8 * r - 4) *
          #(hwZeroQuadruples (hwBlockChoiceFreq k r N (by omega) a)) ≤
        (2 * N) ^ (8 * r - 4) * (K * N ^ (8 * r - k + 4)) := by
          gcongr
          simpa [K, hwStepK] using hzero
      _ = 2 ^ (8 * r - 4) * K * N ^ (16 * r - k) := by
        rw [mul_pow]
        calc
          2 ^ (8 * r - 4) * N ^ (8 * r - 4) *
              (K * N ^ (8 * r - k + 4)) =
            2 ^ (8 * r - 4) * K *
              (N ^ (8 * r - 4) * N ^ (8 * r - k + 4)) := by ring
          _ = _ := by
            rw [← pow_add]
            congr 3
            omega
  have hbracket :
      (((N + 1 : ℕ) : ℝ) ^ (8 * r) +
        ((2 * N : ℕ) : ℝ) ^ (8 * r - 4) *
          #(hwZeroQuadruples (hwBlockChoiceFreq k r N (by omega) a))) ≤
      (2 ^ (8 * r) + 2 ^ (8 * r - 4) * K) *
        (N : ℝ) ^ (16 * r - k) := by
    calc
      _ ≤ 2 ^ (8 * r) * (N : ℝ) ^ (16 * r - k) +
          (2 ^ (8 * r - 4) * K : ℕ) * (N : ℝ) ^ (16 * r - k) := by
        exact add_le_add hdiag (by exact_mod_cast hblockNat)
      _ = _ := by push_cast; ring
  have hPpos : (0 : ℝ) < P := Nat.cast_pos.mpr (NeZero.pos P)
  have hcancel : (#(hwMomentFinset (8 * r) N (hwPolyEval k a)) : ℝ) ≤
      C * N ^ (16 * r - k) := by
    apply le_of_mul_le_mul_left (a := (P : ℝ)) _ hPpos
    calc
      (P : ℝ) * #(hwMomentFinset (8 * r) N (hwPolyEval k a)) =
          ∑ α : ZMod P,
            ‖hwWeylSum P N (hwPolyEval k a) α‖ ^ (16 * r) := by
        rw [← show 2 * (8 * r) = 16 * r by omega]
        exact hmoment.symm
      _ ≤ _ := hpoint
      _ = (P : ℝ) * 2 ^ (8 * r) *
          (((N + 1 : ℕ) : ℝ) ^ (8 * r) +
            ((2 * N : ℕ) : ℝ) ^ (8 * r - 4) *
              #(hwZeroQuadruples
                (hwBlockChoiceFreq k r N (by omega) a))) := hsum
      _ ≤ (P : ℝ) * 2 ^ (8 * r) *
          ((2 ^ (8 * r) + 2 ^ (8 * r - 4) * K) *
            (N : ℝ) ^ (16 * r - k)) := by gcongr
      _ = (P : ℝ) * (C * N ^ (16 * r - k)) := by
        simp [C, hwStepC, K]
        ring
  have hnat : #(hwMomentFinset (8 * r) N (hwPolyEval k a)) ≤
      C * N ^ (16 * r - k) := by exact_mod_cast hcancel
  dsimp [C, r] at hnat ⊢
  rw [← hrel.2.1, ← hrel.2.2.1]
  exact hnat

private theorem hw_exists_moment_bound (k c : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, 0 < C ∧ ∀ (N : ℕ) (a : Fin (k + 1) → ℤ), 0 < N →
      hwCoeffBound k c N a → a ⟨k, by omega⟩ ≠ 0 →
      #(hwMomentFinset (8 ^ (k - 1) / 2) N (hwPolyEval k a)) ≤
        C * N ^ (8 ^ (k - 1) - k) := by
  revert c
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro c
      by_cases hk₂ : k = 2
      · subst k
        simpa using hw_quadratic_moment_bound c
      · have hk₃ : 3 ≤ k := by omega
        obtain ⟨Cᵢ, _, hI₀⟩ :=
          ih (k - 1) (by omega) (by omega) (hwStepD k c)
        obtain ⟨C₄, _, hfour⟩ := hw_exists_fourTermCount_bound
        let C := hwStepC k c Cᵢ C₄
        have hI : ∀ (N : ℕ) (b : Fin (k - 1 + 1) → ℤ), 0 < N →
            hwCoeffBound (k - 1) (hwStepD k c) N b →
              b ⟨k - 1, by omega⟩ ≠ 0 →
            #(hwMomentFinset (8 ^ (k - 2) / 2) N (hwPolyEval (k - 1) b)) ≤
              Cᵢ * N ^ (8 ^ (k - 2) - (k - 1)) := by
          intro N b hN hb hbtop
          have hi := hI₀ N b hN hb hbtop
          rw [show k - 1 - 1 = k - 2 by omega] at hi
          exact hi
        refine ⟨C, ?_, ?_⟩
        · dsimp [C, hwStepC]
          exact Nat.mul_pos (pow_pos (by omega) _)
            (Nat.add_pos_left (pow_pos (by omega) _) _)
        · exact hw_moment_induction_step k c Cᵢ C₄ hk₃ hI hfour

private def hwPowerSumset (k s : ℕ) : Set ℕ :=
  {n | ∃ x : Fin s → ℕ, n = ∑ i, x i ^ k}

private def hwPowerFiber (k s M n : ℕ) : Finset (Fin s → Fin (M + 1)) :=
  Finset.univ.filter fun x ↦ n = ∑ i, (x i : ℕ) ^ k

private def hwSplitTuple (r M : ℕ) (x : Fin (r + r) → Fin (M + 1)) :
    (Fin r → Fin (M + 1)) × (Fin r → Fin (M + 1)) :=
  (fun i ↦ x (Fin.castAdd r i), fun i ↦ x (Fin.natAdd r i))

private def hwPowerCoeffs (k : ℕ) : Fin (k + 1) → ℤ :=
  fun j ↦ if j.val = k then 1 else 0

private theorem hw_exists_powerFiber_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, 0 < C ∧ ∀ M n : ℕ,
      #(hwPowerFiber k (8 ^ (k - 1)) M n) ≤
        C * (M + 1) ^ (8 ^ (k - 1) - k) := by
  obtain ⟨C, hC, hmoment⟩ := hw_exists_moment_bound k 1 hk
  refine ⟨C, hC, ?_⟩
  intro M n
  let s := 8 ^ (k - 1)
  let r := s / 2
  have hsEven : Even s := by
    rw [Nat.even_pow]
    exact ⟨by norm_num, by omega⟩
  have hrs : r + r = s := by
    have h := Nat.two_mul_div_two_of_even hsEven
    omega
  by_cases hM : M = 0
  · subst M
    calc
      #(hwPowerFiber k s 0 n) ≤
          #((Finset.univ : Finset (Fin s → Fin (0 + 1)))) := by
        exact Finset.card_filter_le _ _
      _ = 1 := by simp
      _ ≤ C * (0 + 1) ^ (s - k) := by simp; omega
  · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
    have htop : hwPowerCoeffs k ⟨k, by omega⟩ ≠ 0 := by
      simp [hwPowerCoeffs]
    have hmom := hmoment M (hwPowerCoeffs k) hMpos
      (hw_powerCoeffs_bound k M) htop
    have hpow : hwPolyEval k (hwPowerCoeffs k) = fun x : ℕ ↦ (x : ℤ) ^ k := by
      funext x
      exact hw_polyEval_power k x
    rw [hpow] at hmom
    calc
      #(hwPowerFiber k s M n) ≤
          #(hwSumFiber r M (fun x : ℕ ↦ (x : ℤ) ^ k) n) :=
        hw_powerFiber_card_le_sumFiber hrs
      _ ≤ #(hwMomentFinset r M (fun x : ℕ ↦ (x : ℤ) ^ k)) :=
        hw_sumFiber_card_le_moment r M _ n
      _ ≤ C * M ^ (s - k) := by
        simpa only [s, r] using hmom
      _ ≤ C * (M + 1) ^ (s - k) :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) (s - k))

private def hwPowerImage (k s M : ℕ) : Finset ℕ :=
  (Finset.univ : Finset (Fin s → Fin (M + 1))).image fun x ↦ ∑ i, (x i : ℕ) ^ k

/--
For every `k ≥ 1` there exists `g : ℕ` such that every `n : ℕ` is a sum of `g` `k`th powers: `∃ x
: Fin g → ℕ, n = ∑ i, (x i) ^ k`. Source: D. Hilbert, Beweis für die Darstellbarkeit der ganzen
Zahlen durch eine feste Anzahl n-ter Potenzen (Waringsches Problem), Math. Ann. 67 (1909) 281–305;
textbook in Vaughan, The Hardy-Littlewood Method; general includes minimal g(k).

Proves `Wanted` entry `hilbert_waring`.

Proof: We follow Linnik's elementary route as presented in Tim Jameson's notes: a mean-value
estimate gives positive Schnirelmann density for a bounded power sumset, which is then an additive
basis of finite order by Schnirelmann's inequality.
-/
theorem hilbert_waring :
    ∀ k : ℕ, 0 < k → ∃ g : ℕ, ∀ n : ℕ, ∃ x : Fin g → ℕ,
      n = Finset.univ.sum fun i => (x i) ^ k := by
  intro k hk
  by_cases hk1 : k = 1
  · subst k
    refine ⟨1, fun n ↦ ⟨fun _ ↦ n, ?_⟩⟩
    simp
  · have hk2 : 2 ≤ k := by omega
    obtain ⟨C, hC, hbound⟩ := hw_exists_powerFiber_bound k hk2
    let s := 8 ^ (k - 1)
    let A := hwPowerSumset k s
    let _ : DecidablePred (· ∈ A) := fun n ↦ Classical.propDecidable (n ∈ A)
    have hs : 0 < s := by positivity
    have hA0 : 0 ∈ A := hwPowerSumset_zero_mem hk
    have hσ : 0 < schnirelmannDensity A := by
      simpa only [A, s] using
        hw_power_sumset_density_pos_of_fiber_bound k C hk2 hC hbound
    obtain ⟨h, hbasis⟩ := exists_additive_basis_of_pos_schnirelmannDensity hA0 hσ
    refine ⟨h * s, fun n ↦ ?_⟩
    obtain ⟨z, hzA, hzn⟩ := hbasis n
    have hrep : ∀ i, ∃ x : Fin s → ℕ, z i = ∑ j, x j ^ k := by
      intro i
      exact hzA i
    choose x hx using hrep
    obtain ⟨y, hy⟩ := hw_sum_flatten h s k x
    refine ⟨y, ?_⟩
    calc
      n = ∑ i, z i := hzn
      _ = ∑ i, ∑ j, x i j ^ k := by
        apply Finset.sum_congr rfl
        intro i _
        exact hx i
      _ = ∑ i, y i ^ k := hy.symm

end MathlibExt.NumberTheory.HilbertWaringWanted
