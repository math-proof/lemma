import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[roth_exists_balanced_degrees](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (d : Fin (m + 1) → ℕ)
  (K R : ℕ)
  (δ β η : ℝ)
-- given
  (hd : ∀ h, 2 ≤ d h)
  (hdmono : Monotone d)
  (hchain : ∀ i : Fin m, d i.castSucc ^ K < d i.succ)
  (hβ : 0 < β)
  (hβδ : β ≤ δ)
  (hη : 0 < η)
  (hβm : (m : ℝ) * β ≤ 1)
  (hK : 2 ≤ β * K) :
-- imply
  ∃ r : Fin (m + 1) → ℕ,
    (∀ h, R ≤ r h) ∧ Antitone r ∧
    (∀ i : Fin m, (r i.succ : ℝ) ≤ δ * r i.castSucc) ∧
    (∀ h, d 0 ^ r 0 ≤ d h ^ r h) ∧
    (∑ h, r h) ≤ 2 * r 0 ∧
    (∀ h, ((d h : ℝ) ^ r h) ≤
      Real.rpow ((d 0 : ℝ) ^ r 0) (1 + η)) := by
-- proof
  classical
  have hdone : ∀ h, 1 ≤ d h := fun h ↦ (by norm_num : (1 : ℕ) ≤ 2).trans (hd h)
  have hd0 : 1 < d 0 := lt_of_lt_of_le Nat.one_lt_two (hd 0)
  choose e he using fun h : Fin (m + 1) ↦ pow_unbounded_of_one_lt (d h) hd0
  let E := ∑ h, e h
  let R' := max R ⌈2 / β⌉₊
  let B := ∑ h, d h ^ R'
  obtain ⟨s₀, hs₀⟩ := pow_unbounded_of_one_lt B hd0
  obtain ⟨s₁, hs₁⟩ := exists_nat_ge ((E : ℝ) / η)
  let s := max 1 (max s₀ s₁)
  have hspos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hs₀s : s₀ ≤ s := (le_max_left s₀ s₁).trans
    (le_max_right 1 (max s₀ s₁))
  have hs₁s : s₁ ≤ s := (le_max_right s₀ s₁).trans
    (le_max_right 1 (max s₀ s₁))
  have hBpow : B < d 0 ^ s := hs₀.trans_le
    (pow_le_pow_right₀ (by omega : 1 ≤ d 0) hs₀s)
  have hEη : (E : ℝ) ≤ η * s := by
    have hs₁R : (s₁ : ℝ) ≤ s := by exact_mod_cast hs₁s
    have hηne : η ≠ 0 := hη.ne'
    calc
      _ = η * ((E : ℝ) / η) := by field_simp
      _ ≤ η * s₁ := mul_le_mul_of_nonneg_left hs₁ hη.le
      _ ≤ η * s := mul_le_mul_of_nonneg_left hs₁R hη.le
  have hceil : 2 / β ≤ (⌈2 / β⌉₊ : ℝ) := Nat.le_ceil _
  have hR'β : 2 ≤ β * R' := by
    have hcR : (⌈2 / β⌉₊ : ℝ) ≤ R' := by
      exact_mod_cast (le_max_right R ⌈2 / β⌉₊)
    calc
      _ = β * (2 / β) := by field_simp
      _ ≤ β * (⌈2 / β⌉₊ : ℝ) := mul_le_mul_of_nonneg_left hceil hβ.le
      _ ≤ β * R' := mul_le_mul_of_nonneg_left hcR hβ.le
  have hR'pos : 0 < R' := by
    by_contra hnot
    have hz : R' = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hz, Nat.cast_zero, mul_zero] at hR'β
    norm_num at hR'β
  have hexists : ∀ h : Fin (m + 1), ∃ n, d 0 ^ s ≤ d h ^ n := by
    intro h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (d 0 ^ s)
      (lt_of_lt_of_le Nat.one_lt_two (hd h))
    exact ⟨n, hn.le⟩
  let r : Fin (m + 1) → ℕ := fun h ↦ Nat.find (hexists h)
  have hrpow : ∀ h, d 0 ^ s ≤ d h ^ r h := fun h ↦ Nat.find_spec (hexists h)
  have hrmin : ∀ h n, d 0 ^ s ≤ d h ^ n → r h ≤ n :=
    fun h n hn ↦ Nat.find_min' (hexists h) hn
  have hrzero : r 0 = s := by
    apply le_antisymm (hrmin 0 s le_rfl)
    exact (Nat.pow_le_pow_iff_right hd0).mp (hrpow 0)
  have hR'large : ∀ h, R' ≤ r h := by
    intro h
    by_contra hnot
    have hrR : r h ≤ R' := Nat.le_of_lt (lt_of_not_ge hnot)
    refine (not_lt_of_ge ((hrpow h).trans
      ((pow_le_pow_right₀ (hdone h) hrR).trans ?_))) hBpow
    have ht := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin (m + 1) ↦ d j ^ R')
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ h)
    simpa [B] using ht
  have hrlarge : ∀ h, R ≤ r h := fun h ↦
    (le_max_left R ⌈2 / β⌉₊).trans (hR'large h)
  have hranti : Antitone r := by
    intro i j hij
    apply hrmin j (r i)
    exact (hrpow i).trans (by gcongr; exact hdmono hij)
  have hβr : ∀ h, 2 ≤ β * r h := by
    intro h
    exact hR'β.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast hR'large h : (R' : ℝ) ≤ r h) hβ.le)
  have hKpos : 0 < K := by
    by_contra hnot
    have hz : K = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hz, Nat.cast_zero, mul_zero] at hK
    norm_num at hK
  have hsepβ : ∀ i : Fin m, (r i.succ : ℝ) ≤ β * r i.castSucc := by
    intro i
    let t := r i.castSucc / K + 1
    have hrit : r i.castSucc ≤ K * t := by
      dsimp [t]
      exact (Nat.lt_mul_div_succ (r i.castSucc) hKpos).le
    have hcandidate : d 0 ^ s ≤ d i.succ ^ t := calc
      _ ≤ d i.castSucc ^ r i.castSucc := hrpow i.castSucc
      _ ≤ d i.castSucc ^ (K * t) :=
        pow_le_pow_right₀ (hdone i.castSucc) hrit
      _ = (d i.castSucc ^ K) ^ t := by rw [pow_mul]
      _ ≤ d i.succ ^ t := by gcongr; exact (hchain i).le
    have hrnext : r i.succ ≤ t := hrmin i.succ t hcandidate
    have hKreal : (0 : ℝ) < K := by exact_mod_cast hKpos
    have hdiv : (1 : ℝ) / K ≤ β / 2 := by
      apply (div_le_iff₀ hKreal).2
      nlinarith
    have hfirst : (r i.castSucc : ℝ) / K ≤
        β * r i.castSucc / 2 := calc
      _ = (r i.castSucc : ℝ) * (1 / K) := by ring
      _ ≤ (r i.castSucc : ℝ) * (β / 2) := by gcongr
      _ = β * r i.castSucc / 2 := by ring
    have hsecond : (1 : ℝ) ≤ β * r i.castSucc / 2 := by
      nlinarith [hβr i.castSucc]
    calc
      _ ≤ (t : ℝ) := by exact_mod_cast hrnext
      _ = ((r i.castSucc / K : ℕ) : ℝ) + 1 := by simp [t]
      _ ≤ (r i.castSucc : ℝ) / K + 1 := by
        gcongr
        exact Nat.cast_div_le
      _ ≤ β * r i.castSucc := by linarith
  have hsep : ∀ i : Fin m, (r i.succ : ℝ) ≤ δ * r i.castSucc := by
    intro i
    exact (hsepβ i).trans
      (mul_le_mul_of_nonneg_right hβδ (Nat.cast_nonneg _))
  have hsum : (∑ h, r h) ≤ 2 * r 0 := by
    have htail : ∀ i : Fin m, (r i.succ : ℝ) ≤ β * r 0 := by
      intro i
      exact (hsepβ i).trans (mul_le_mul_of_nonneg_left
        (by exact_mod_cast hranti (Fin.zero_le i.castSucc)) hβ.le)
    have hsumR : ((∑ h, r h : ℕ) : ℝ) ≤ 2 * (r 0 : ℝ) := by
      rw [Fin.sum_univ_succ, Nat.cast_add, Nat.cast_sum]
      calc
        _ ≤ (r 0 : ℝ) + ∑ _ : Fin m, β * r 0 := by gcongr with i; exact htail i
        _ = (r 0 : ℝ) + (m : ℝ) * (β * r 0) := by simp
        _ ≤ 2 * (r 0 : ℝ) := by
          have hr0nonneg : (0 : ℝ) ≤ r 0 := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hβm hr0nonneg]
    exact_mod_cast hsumR
  refine ⟨r, hrlarge, hranti, hsep, fun h ↦ by simpa [hrzero] using hrpow h,
    hsum, ?_⟩
  intro h
  have hrpos : 0 < r h := hR'pos.trans_le (hR'large h)
  have hpred : d h ^ (r h - 1) < d 0 ^ s := by
    apply lt_of_not_ge
    exact Nat.find_min (hexists h) (Nat.sub_lt (Nat.zero_lt_of_lt hrpos) Nat.zero_lt_one)
  have hstep : d h ^ r h < d 0 ^ s * d h := calc
    _ = d h ^ (r h - 1) * d h := by
      conv_lhs => rw [show r h = (r h - 1) + 1 by omega, pow_succ]
    _ < d 0 ^ s * d h := Nat.mul_lt_mul_of_pos_right hpred
      (lt_of_lt_of_le Nat.zero_lt_two (hd h))
  have heE : e h ≤ E := by
    have ht := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin (m + 1) ↦ e j)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ h)
    simpa [E] using ht
  have hdE : d h ≤ d 0 ^ E :=
    (he h).le.trans (pow_le_pow_right₀ hd0.le heE)
  have hnat : d h ^ r h ≤ d 0 ^ (s + E) := calc
    _ ≤ d 0 ^ s * d h := hstep.le
    _ ≤ d 0 ^ s * d 0 ^ E := Nat.mul_le_mul_left _ hdE
    _ = d 0 ^ (s + E) := (pow_add _ _ _).symm
  have hexp : ((s + E : ℕ) : ℝ) ≤ (s : ℝ) * (1 + η) := by
    push_cast
    nlinarith
  calc
    _ = ((d h ^ r h : ℕ) : ℝ) := by norm_num
    _ ≤ ((d 0 ^ (s + E) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (d 0 : ℝ) ^ (s + E) := by norm_cast
    _ = Real.rpow (d 0 : ℝ) (s + E : ℕ) :=
      (Real.rpow_natCast _ _).symm
    _ ≤ Real.rpow (d 0 : ℝ) ((s : ℝ) * (1 + η)) :=
      Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (hdone 0) : (1 : ℝ) ≤ d 0) hexp
    _ = Real.rpow (Real.rpow (d 0 : ℝ) (s : ℝ)) (1 + η) :=
      Real.rpow_mul (by positivity) _ _
    _ = Real.rpow ((d 0 : ℝ) ^ s) (1 + η) := by
      congr 1
      exact Real.rpow_natCast _ _
    _ = Real.rpow ((d 0 : ℝ) ^ r 0) (1 + η) := by rw [hrzero]


-- created on 2026-10-21
