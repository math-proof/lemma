import Mathlib
import sympy.Basic
import Def.v1.Atlas.BooleanFunctions.code.Stability
open Finset BigOperators Real BooleanFourier


namespace BooleanFourier

/--
[noiseOperator_eq_fourier_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Stability.lean)
-/
@[path]
lemma noiseOperator_eq_fourier_sum
  {n : ℕ}
  {ρ : ℝ}
  {f : (Fin n → Bool) → ℝ}
  {x : Fin n → Bool} :
-- imply
  noiseOperator ρ f x = ∑ S : Finset (Fin n), ρ ^ S.card * fourierCoeff f S * chi S x :=
-- proof
noiseOp_eq_fourier_expansion ρ f x

end BooleanFourier

namespace BooleanFourier

/--
[sum_chi_mul_chi_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Stability.lean)
-/
@[path]
lemma sum_chi_mul_chi_eq
  {n : ℕ}
  {S T : Finset (Fin n)} :
-- imply
  ∑ x : Fin n → Bool, chi S x * chi T x = if S = T then (2 : ℝ) ^ n else 0 := by
-- proof
  classical
  split_ifs with h
  · subst h
    simp_rw [chi_mul_self]
    simp [Fintype.card_bool, Fintype.card_fin]
  ·
    have hne : ∃ j, (j ∈ S ∧ j ∉ T) ∨ (j ∈ T ∧ j ∉ S) := by
      by_contra hall
      push Not at hall
      have heq : S = T := by
        ext j
        constructor
        · intro hj
          exact by_contra (fun hnjT => hnjT ((hall j).1 hj))
        · intro hj
          exact by_contra (fun hnjS => hnjS ((hall j).2 hj))
      exact h heq
    obtain ⟨j, hj_mem⟩ := hne
    apply Finset.sum_ninvolution (g := fun x => flipAt j x)
    · intro x
      cases hj_mem with
      | inl hjST =>
        have hflip : chi S (flipAt j x) * chi T (flipAt j x) =
          -(chi S x * chi T x) := by
          rw [chi_flipAt S j hjST.1 x]
          have hT : chi T (flipAt j x) = chi T x := by
            simp only [chi, flipAt]
            apply Finset.prod_congr rfl
            intro i hi
            congr 1
            exact Function.update_of_ne (ne_of_mem_of_not_mem hi hjST.2) _ _
          rw [hT]; ring
        linarith
      | inr hjTS =>
        have hflip : chi S (flipAt j x) * chi T (flipAt j x) =
          -(chi S x * chi T x) := by
          rw [chi_flipAt T j hjTS.1 x]
          have hS : chi S (flipAt j x) = chi S x := by
            simp only [chi, flipAt]
            apply Finset.prod_congr rfl
            intro i hi
            congr 1
            exact Function.update_of_ne (ne_of_mem_of_not_mem hi hjTS.2) _ _
          rw [hS]; ring
        linarith
    · intro x _
      exact flipAt_ne_self j x
    · intro x
      exact Finset.mem_univ _
    · intro x
      exact flipAt_flipAt j x

end BooleanFourier

namespace BooleanFourier

/--
[noiseStability_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Stability.lean)
-/
@[path]
lemma noiseStability_eq_sum
  {n : ℕ}
  {ρ : ℝ}
  {f : (Fin n → Bool) → ℝ} :
-- imply
  noiseStability ρ f = ∑ S : Finset (Fin n), ρ ^ S.card * fourierCoeff f S ^ 2 := by
-- proof
  classical
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num : (0 : ℝ) < 2) n
  have h2n_ne : (2 : ℝ) ^ n ≠ 0 := ne_of_gt h2n_pos
  simp only [noiseStability]
  simp_rw [noiseOperator_eq_fourier_sum]
  conv_lhs =>
    arg 2; arg 2; ext x
    rw [fourier_expansion f x]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (s := univ (α := Fin n → Bool))]
  simp_rw [Finset.sum_comm (s := univ (α := Fin n → Bool))]
  simp_rw [show ∀ (T S : Finset (Fin n)) (x : Fin n → Bool),
    fourierCoeff f T * chi T x * (ρ ^ S.card * fourierCoeff f S * chi S x) =
    (fourierCoeff f T * ρ ^ S.card * fourierCoeff f S) * (chi T x * chi S x)
    from fun T S x => by ring]
  simp_rw [← Finset.mul_sum]
  simp_rw [sum_chi_mul_chi_eq]
  simp_rw [mul_ite, mul_zero]
  simp_rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  rw [show (1 : ℝ) / 2 ^ n * ∑ x : Finset (Fin n),
    fourierCoeff f x * ρ ^ x.card * fourierCoeff f x * 2 ^ n =
    ∑ x : Finset (Fin n), 1 / 2 ^ n *
      (fourierCoeff f x * ρ ^ x.card * fourierCoeff f x * 2 ^ n) from
    Finset.mul_sum ..]
  congr 1; ext S
  field_simp

end BooleanFourier

namespace BooleanFourier

/--
[lpNorm_four_pow_le_of_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Stability.lean)
-/
@[path]
lemma lpNorm_four_pow_le_of_degree
  {n : ℕ}
  {f : BoolFn n}
  {d : ℕ}
-- given
  (hdeg : ∀ S : Finset (Fin n), S.card > d → fourierCoeff f S = 0) :
-- imply
  lpNorm 4 f ^ 4 ≤ (9 : ℝ) ^ d * lpNorm 2 f ^ 4 := by
-- proof
  open Real in
  have hdeg' : degree f ≤ d := by
    unfold degree
    apply Finset.sup_le
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    by_contra h
    push Not at h
    exact hS (hdeg S h)
  have h_bb : ∀ (g : BoolFn n) (ρ' : ℝ),
    0 ≤ ρ' → ρ' ≤ Real.sqrt ((2 - 1) / ((4 : ℝ) - 1)) →
    lpNorm 4 (noiseOp ρ' g) ≤ lpNorm 2 g := by
    intro g ρ' hρ'_nonneg hρ'_bound
    exact bonami_beckner g (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 4)
      hρ'_nonneg hρ'_bound
  have h_hyp := hypercontractive_low_degree f d 4 (by norm_num : (2 : ℝ) ≤ 4) hdeg' h_bb
  have h_lpNorm4_nonneg : (0 : ℝ) ≤ lpNorm 4 f := by
    unfold lpNorm
    apply rpow_nonneg
    apply mul_nonneg
    · positivity
    · exact Finset.sum_nonneg (fun x _ => rpow_nonneg (abs_nonneg _) _)
  have h_pow4 : lpNorm 4 f ^ 4 ≤ ((4 - 1 : ℝ) ^ ((↑d : ℝ) / 2) * lpNorm 2 f) ^ 4 :=
    pow_le_pow_left₀ h_lpNorm4_nonneg h_hyp 4
  rw [mul_pow] at h_pow4
  suffices h_eq : ((4 - 1 : ℝ) ^ ((↑d : ℝ) / 2)) ^ 4 = (9 : ℝ) ^ d by
    calc lpNorm 4 f ^ 4
      ≤ ((4 - 1 : ℝ) ^ ((↑d : ℝ) / 2)) ^ 4 * lpNorm 2 f ^ 4 := h_pow4
      _ = (9 : ℝ) ^ d * lpNorm 2 f ^ 4 := by rw [h_eq]
  have h3 : (4 : ℝ) - 1 = 3 := by norm_num
  rw [h3]
  rw [← rpow_natCast ((3 : ℝ) ^ ((↑d : ℝ) / 2)) 4]
  rw [← rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have h_exp : (↑d : ℝ) / 2 * (↑(4 : ℕ) : ℝ) = (↑(2 * d) : ℝ) := by push_cast; ring
  rw [h_exp, rpow_natCast]
  rw [show (3 : ℝ) ^ (2 * d) = ((3 : ℝ) ^ 2) ^ d from pow_mul (3 : ℝ) 2 d]
  norm_num

end BooleanFourier

namespace BooleanFourier

/--
[lpNorm_rpow_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Stability.lean)
-/
@[path]
lemma lpNorm_rpow_eq
  {n : ℕ}
  {f : BoolFn n}
  {p : ℝ}
-- given
  (hp : 0 < p) :
-- imply
  lpNorm p f ^ p = (1 / (2 ^ n : ℝ)) * ∑ x : Fin n → Bool, := by
-- proof
  unfold lpNorm
  rw [← rpow_mul (by positivity : (0 : ℝ) ≤ (1 / 2 ^ n) *
    ∑ x : Fin n → Bool, |f x| ^ p)]
  simp [hp.ne']

end BooleanFourier

namespace BooleanFourier

/--
[anticoncentration_thm38](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Stability.lean)
-/
@[path]
lemma anticoncentration_thm38
  {n : ℕ}
  {f : BoolFn n}
  {d : ℕ}
  {θ : ℝ}
-- given
  (hdeg : ∀ S : Finset (Fin n), S.card > d → fourierCoeff f S = 0)
  (hθ0 : 0 < θ)
  (hθ1 : θ < 1) :
-- imply
  (Finset.univ.filter (fun x : Fin n → Bool => |f x| ≥ θ * lpNorm 2 f)).card / (2 ^ n : ℝ) ≥ (1 - θ ^ 2) ^ 2 / (9 : ℝ) ^ d := by
-- proof
  by_cases hf : lpNorm 2 f = 0
  ·
    simp only [hf, mul_zero]
    have hcard : (Finset.univ.filter (fun x : Fin n → Bool => |f x| ≥ 0)).card =
      Fintype.card (Fin n → Bool) := by
      congr 1; ext x; simp [abs_nonneg]
    rw [hcard, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    have h2n_pos : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num : (0 : ℝ) < 2) n
    rw [show (↑(2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n from by push_cast; ring]
    rw [div_self (ne_of_gt h2n_pos)]
    rw [ge_iff_le]
    apply div_le_one_of_le₀
    · have h1 : (1 - θ ^ 2) ^ 2 ≤ 1 := by
      have hθsq : θ ^ 2 < 1 := by nlinarith
      nlinarith [sq_nonneg (1 - θ ^ 2)]
      have h9 : (1 : ℝ) ≤ (9 : ℝ) ^ d := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 9)
      linarith
    · positivity
  ·
    have hlp2_pos : (0 : ℝ) < lpNorm 2 f := by
      rcases lt_or_eq_of_le (show (0 : ℝ) ≤ lpNorm 2 f from by unfold lpNorm; positivity)
        with h | h
      · exact h
      · exact absurd h.symm hf
    have h2n_pos : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num : (0 : ℝ) < 2) n
    have h9d_pos : (0 : ℝ) < (9 : ℝ) ^ d := pow_pos (by norm_num : (0 : ℝ) < 9) d
    set A := Finset.univ.filter (fun x : Fin n → Bool => |f x| ≥ θ * lpNorm 2 f)
    rw [ge_iff_le]
    rw [div_le_div_iff₀ h9d_pos h2n_pos]
    have h_comp : ∑ x ∈ Finset.univ.filter (fun x => ¬ (|f x| ≥ θ * lpNorm 2 f)),
      (f x) ^ 2 ≤ θ ^ 2 * lpNorm 2 f ^ 2 * 2 ^ n := by
      have hbd : ∀ x ∈ Finset.univ.filter (fun x => ¬ (|f x| ≥ θ * lpNorm 2 f)),
        (f x) ^ 2 ≤ θ ^ 2 * lpNorm 2 f ^ 2 := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hx
        have : (f x) ^ 2 = |f x| ^ 2 := (sq_abs _).symm
        rw [this]
        have hle : |f x| ≤ θ * lpNorm 2 f := le_of_lt hx
        nlinarith [sq_nonneg (θ * lpNorm 2 f - |f x|), abs_nonneg (f x),
          sq_abs (f x), mul_self_nonneg (θ * lpNorm 2 f)]
      calc ∑ x ∈ Finset.univ.filter (fun x => ¬ (|f x| ≥ θ * lpNorm 2 f)), (f x) ^ 2
        ≤ ∑ x ∈ Finset.univ.filter (fun x => ¬ (|f x| ≥ θ * lpNorm 2 f)),
          (θ ^ 2 * lpNorm 2 f ^ 2) :=
          Finset.sum_le_sum hbd
        _ = (Finset.univ.filter (fun x => ¬ (|f x| ≥ θ * lpNorm 2 f))).card *
          (θ ^ 2 * lpNorm 2 f ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ Fintype.card (Fin n → Bool) * (θ ^ 2 * lpNorm 2 f ^ 2) := by
          apply mul_le_mul_of_nonneg_right
          · exact Nat.cast_le.mpr (Finset.card_filter_le _ _)
          · positivity
        _ = θ ^ 2 * lpNorm 2 f ^ 2 * 2 ^ n := by
          simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
          push_cast; ring
    have h_sum_sq : ∑ x : Fin n → Bool, (f x) ^ 2 = lpNorm 2 f ^ 2 * 2 ^ n := by
      have h := lpNorm_rpow_eq f (by norm_num : (0 : ℝ) < 2)
      have h_abs : ∀ x : Fin n → Bool, |f x| ^ (2 : ℝ) = (f x) ^ 2 := by
        intro x; rw [show (2 : ℝ) = ↑(2 : ℕ) from by norm_num, rpow_natCast]; exact sq_abs _
      simp_rw [h_abs] at h
      rw [show lpNorm 2 f ^ 2 = lpNorm 2 f ^ (2 : ℝ) from by
        rw [show (2 : ℝ) = ↑(2 : ℕ) from by norm_num, rpow_natCast]]
      field_simp at h ⊢; linarith
    have h_on_A : (1 - θ ^ 2) * (lpNorm 2 f ^ 2 * 2 ^ n) ≤ ∑ x ∈ A, (f x) ^ 2 := by
      have hsplit := (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x => |f x| ≥ θ * lpNorm 2 f) (fun x => (f x) ^ 2)).symm
      linarith [h_sum_sq, h_comp]
    have h_cs : (∑ x ∈ A, (f x) ^ 2) ^ 2 ≤ (A.card : ℝ) * ∑ x ∈ A, (f x) ^ 4 := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq A (fun _ => (1 : ℝ)) (fun x => (f x) ^ 2)
      have heq1 : (∑ _x ∈ A, (1 : ℝ) ^ 2) = (A.card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      have heq2 : ∀ x, ((f x) ^ 2) ^ 2 = (f x) ^ 4 := fun x => by ring
      simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
      calc (∑ x ∈ A, (f x) ^ 2) ^ 2 ≤ (↑A.card : ℝ) * ∑ x ∈ A, ((f x) ^ 2) ^ 2 := h
        _ = (A.card : ℝ) * ∑ x ∈ A, (f x) ^ 4 := by
          congr 1; exact Finset.sum_congr rfl (fun x _ => heq2 x)
    have h_sum_fourth_bound : ∑ x ∈ A, (f x) ^ 4 ≤ (9 : ℝ) ^ d * lpNorm 2 f ^ 4 * 2 ^ n := by
      have h_sub : ∑ x ∈ A, (f x) ^ 4 ≤ ∑ x : Fin n → Bool, (f x) ^ 4 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun x _ _ => by positivity)
      have h_sum_fourth_eq : ∑ x : Fin n → Bool, (f x) ^ 4 = lpNorm 4 f ^ 4 * 2 ^ n := by
        have h := lpNorm_rpow_eq f (by norm_num : (0 : ℝ) < 4)
        have h_abs : ∀ x : Fin n → Bool, |f x| ^ (4 : ℝ) = (f x) ^ 4 := by
          intro x
          rw [show (4 : ℝ) = ↑(4 : ℕ) from by norm_num, rpow_natCast]
          have : |f x| ^ 4 = (f x) ^ 4 := by
            rw [show |f x| ^ 4 = (|f x| ^ 2) ^ 2 from by ring]
            rw [sq_abs]
            ring
          exact this
        simp_rw [h_abs] at h
        rw [show lpNorm 4 f ^ 4 = lpNorm 4 f ^ (4 : ℝ) from by
          rw [show (4 : ℝ) = ↑(4 : ℕ) from by norm_num, rpow_natCast]]
        field_simp at h ⊢; linarith
      have h_l4 := lpNorm_four_pow_le_of_degree f d hdeg
      nlinarith [h_sub, h_sum_fourth_eq]
    set S_A := ∑ x ∈ A, (f x) ^ 2
    have hSA_nonneg : 0 ≤ S_A := Finset.sum_nonneg (fun x _ => sq_nonneg _)
    have hSA_lower : (1 - θ ^ 2) * (lpNorm 2 f ^ 2 * 2 ^ n) ≤ S_A := h_on_A
    have hSA_sq_upper : S_A ^ 2 ≤ (A.card : ℝ) * ((9 : ℝ) ^ d * lpNorm 2 f ^ 4 * 2 ^ n) := by
      calc S_A ^ 2 ≤ (A.card : ℝ) * ∑ x ∈ A, (f x) ^ 4 := h_cs
        _ ≤ (A.card : ℝ) * ((9 : ℝ) ^ d * lpNorm 2 f ^ 4 * 2 ^ n) := by
          apply mul_le_mul_of_nonneg_left h_sum_fourth_bound
          exact Nat.cast_nonneg' A.card
    have hSA_lower_sq : ((1 - θ ^ 2) * (lpNorm 2 f ^ 2 * 2 ^ n)) ^ 2 ≤ S_A ^ 2 := by
      have h1θ : 0 ≤ (1 - θ ^ 2) * (lpNorm 2 f ^ 2 * 2 ^ n) := by
        apply mul_nonneg
        · nlinarith [sq_nonneg θ]
        · positivity
      nlinarith [sq_nonneg (S_A - (1 - θ ^ 2) * (lpNorm 2 f ^ 2 * 2 ^ n))]
    have h_combined : ((1 - θ ^ 2) * (lpNorm 2 f ^ 2 * 2 ^ n)) ^ 2 ≤
      (↑A.card : ℝ) * (9 ^ d * lpNorm 2 f ^ 4 * 2 ^ n) :=
      le_trans hSA_lower_sq hSA_sq_upper
    nlinarith [sq_nonneg (lpNorm 2 f), h2n_pos, hlp2_pos,
      mul_pos (mul_pos (pow_pos hlp2_pos 4) h2n_pos) h2n_pos]

end BooleanFourier

namespace BooleanFourier

/--
[degree_le_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Stability.lean)
-/
@[path]
lemma degree_le_iff
  {n : ℕ}
  {f : BoolFn n}
  {d : ℕ} :
-- imply
  degree f ≤ d ↔ ∀ S : Finset (Fin n), S.card > d → fourierCoeff f S = 0 := by
-- proof
  unfold degree
  constructor
  · intro h S hS
    by_contra hne
    have hS_mem : S ∈ Finset.univ.filter (fun S : Finset (Fin n) => fourierCoeff f S ≠ 0) := by
      simp [hne]
    have := Finset.le_sup hS_mem (f := Finset.card)
    omega
  · intro h
    apply Finset.sup_le
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    by_contra hlt
    push_neg at hlt
    exact hS (h S (by omega))

end BooleanFourier

namespace BooleanFourier

/--
[anticoncentration_low_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Stability.lean)
-/
@[path]
lemma anticoncentration_low_degree
  {n : ℕ}
  {f : BoolFn n}
  {δ : ℝ}
-- given
  (hf01 : ∀ x : Fin n → Bool, f x = 0 ∨ f x = 1)
  (hδ_pos : 0 < δ)
  (hδ_le : δ ≤ 1)
  (hδ_eq : (Finset.univ.filter (fun x : Fin n → Bool => f x = 1)).card / (2 ^ n : ℝ) = δ) :
-- imply
  (degree f : ℝ) ≥ Real.log (1 / δ) / Real.log 9 := by
-- proof
  set d := degree f
  have h2n_pos : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num : (0:ℝ) < 2) n
  have h9d_pos : (0 : ℝ) < (9 : ℝ) ^ d := pow_pos (by norm_num : (0:ℝ) < 9) d
  have hdeg : ∀ S : Finset (Fin n), S.card > d → fourierCoeff f S = 0 :=
    (degree_le_iff f d).mp le_rfl
  have hcard_eq : ↑(Finset.univ.filter (fun x : Fin n → Bool => f x = 1)).card = δ * 2 ^ n := by
    have := hδ_eq; field_simp at this ⊢; linarith
  have hlp2_sq : lpNorm 2 f ^ 2 = δ := by
    have h := lpNorm_rpow_eq f (by norm_num : (0 : ℝ) < 2)
    rw [show lpNorm 2 f ^ 2 = lpNorm 2 f ^ (2 : ℝ) from by
      rw [show (2 : ℝ) = ↑(2 : ℕ) from by norm_num, rpow_natCast]]
    rw [h]
    have h_abs : ∀ x : Fin n → Bool, |f x| ^ (2 : ℝ) = f x := by
      intro x
      rw [show (2:ℝ) = ↑(2:ℕ) from by norm_num, rpow_natCast]
      obtain hx | hx <;> simp [hx] := hf01 x
    simp_rw [h_abs]
    have hsum : ∑ x : Fin n → Bool, f x =
      ↑(Finset.univ.filter (fun x : Fin n → Bool => f x = 1)).card := by
      conv_lhs =>
        rw [show (∑ x : Fin n → Bool, f x) =
          ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => f x = 1), f x +
          ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => ¬(f x = 1)), f x from
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm]
      have h0 : ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => ¬(f x = 1)), f x = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        obtain h | h := hf01 x
        · exact h
        · exact absurd h hx
      have h1 : ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => f x = 1), f x =
        ↑(Finset.univ.filter (fun x : Fin n → Bool => f x = 1)).card := by
        conv_lhs =>
          rw [show (∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => f x = 1), f x) =
            ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => f x = 1), (1 : ℝ) from
            Finset.sum_congr rfl (fun x hx => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx; exact hx)]
        simp [Finset.sum_const, nsmul_eq_mul]
      linarith
    rw [hsum, hcard_eq]; field_simp
  have hlp2_pos : (0 : ℝ) < lpNorm 2 f := by
    have h1 : lpNorm 2 f ^ 2 = δ := hlp2_sq
    have h2 : (0 : ℝ) ≤ lpNorm 2 f := by unfold lpNorm; positivity
    nlinarith [sq_nonneg (lpNorm 2 f)]
  have hlp2_le_one : lpNorm 2 f ≤ 1 := by
    nlinarith [hlp2_sq, sq_nonneg (lpNorm 2 f - 1)]
  have hfilter_eq : ∀ θ : ℝ, 0 < θ → θ < 1 →
    (Finset.univ.filter (fun x : Fin n → Bool => |f x| ≥ θ * lpNorm 2 f)) =
    (Finset.univ.filter (fun x : Fin n → Bool => f x = 1)) := by
    intro θ hθ0 hθ1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hge
      obtain hx | hx := hf01 x
      · simp [hx] at hge
        linarith [mul_pos hθ0 hlp2_pos]
      · exact hx
    · intro hx
      rw [hx, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
      calc (1 : ℝ) ≥ lpNorm 2 f := hlp2_le_one
        _ ≥ θ * lpNorm 2 f := by nlinarith
  have hbound : ∀ θ : ℝ, 0 < θ → θ < 1 → δ ≥ (1 - θ ^ 2) ^ 2 / (9 : ℝ) ^ d := by
    intro θ hθ0 hθ1
    have hanti := anticoncentration_thm38 f d hdeg θ hθ0 hθ1
    rw [hfilter_eq θ hθ0 hθ1] at hanti
    linarith [hδ_eq]
  suffices hmain : 1 ≤ δ * (9 : ℝ) ^ d by
    rw [ge_iff_le]
    have hlog9_pos : (0 : ℝ) < Real.log 9 := by
      apply Real.log_pos; norm_num
    rw [div_le_iff₀ hlog9_pos]
    have h9d_ge : (9 : ℝ) ^ d ≥ 1 / δ := by
      rw [ge_iff_le, div_le_iff₀ hδ_pos]; linarith
    calc Real.log (1 / δ) ≤ Real.log ((9 : ℝ) ^ d) := by
      apply Real.log_le_log (by positivity) h9d_ge
      _ = ↑d * Real.log 9 := by
        rw [Real.log_pow]
      _ = (↑d : ℝ) * Real.log 9 := by ring
  by_contra hlt
  push_neg at hlt
  set c := δ * (9 : ℝ) ^ d
  have hc_pos : (0 : ℝ) < c := mul_pos hδ_pos h9d_pos
  have hc_lt_one : c < 1 := hlt
  have hbd2 : ∀ θ : ℝ, 0 < θ → θ < 1 → (1 - θ ^ 2) ^ 2 ≤ c := by
    intro θ hθ0 hθ1
    have := hbound θ hθ0 hθ1
    rw [ge_iff_le, div_le_iff₀ h9d_pos] at this
    linarith
  have hε_pos : (0 : ℝ) < 1 - c := by linarith
  set ε := 1 - c
  have hε3_pos : (0 : ℝ) < ε / 3 := by linarith
  have hε3_lt_one : ε / 3 < 1 := by linarith [show ε ≤ 1 from by linarith [hc_pos]]
  set θ := Real.sqrt (ε / 3)
  have hθ_pos : (0 : ℝ) < θ := Real.sqrt_pos_of_pos hε3_pos
  have hθ_lt_one : θ < 1 := by
    rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (le_of_lt hε3_pos) hε3_lt_one
  have hθ_sq : θ ^ 2 = ε / 3 := by
    rw [sq, show θ * θ = θ ^ 2 from by ring]
    exact Real.sq_sqrt (le_of_lt hε3_pos)
  have h_val : (1 - θ ^ 2) ^ 2 = ((2 + c) / 3) ^ 2 := by
    rw [hθ_sq]; ring_nf; ring
  have h_ineq : ((2 + c) / 3) ^ 2 > c := by
    rw [div_pow, show (3:ℝ) ^ 2 = 9 from by norm_num]
    rw [gt_iff_lt, lt_div_iff₀ (by norm_num : (0:ℝ) < 9)]
    nlinarith [sq_nonneg (c - 1), sq_nonneg c]
  have h_contra := hbd2 θ hθ_pos hθ_lt_one
  linarith [h_val]

end BooleanFourier


-- created on 2026-10-23
