import Mathlib
import Def.TateCurve_QSeries

set_option autoImplicit false

open scoped NNReal
open IsUltrametricDist Filter

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

section Ultrametric

theorem nnnorm_one_sub_of_lt_one {x : K} (hx : ‖x‖₊ < 1) : ‖1 - x‖₊ = 1 := by
  have h : ‖(1 : K)‖₊ ≠ ‖-x‖₊ := by
    rw [nnnorm_neg, nnnorm_one]
    exact (ne_of_lt hx).symm
  rw [sub_eq_add_neg, nnnorm_add_eq_max_of_nnnorm_ne_nnnorm h, nnnorm_neg, nnnorm_one]
  exact max_eq_left hx.le

theorem one_sub_ne_zero_of_lt_one {x : K} (hx : ‖x‖₊ < 1) : (1 : K) - x ≠ 0 := by
  intro h
  have := nnnorm_one_sub_of_lt_one hx
  rw [h, nnnorm_zero] at this
  exact zero_ne_one this

theorem nnnorm_eq_of_nnnorm_sub_lt {a b : K} (h : ‖a - b‖₊ < ‖b‖₊) : ‖a‖₊ = ‖b‖₊ := by
  have hne : ‖a - b‖₊ ≠ ‖b‖₊ := ne_of_lt h
  calc ‖a‖₊ = ‖a - b + b‖₊ := by rw [sub_add_cancel]
    _ = max ‖a - b‖₊ ‖b‖₊ := nnnorm_add_eq_max_of_nnnorm_ne_nnnorm hne
    _ = ‖b‖₊ := max_eq_right h.le

theorem nnnorm_add_le_of_le {a b : K} {C : NNReal} (ha : ‖a‖₊ ≤ C) (hb : ‖b‖₊ ≤ C) :
    ‖a + b‖₊ ≤ C :=
  (nnnorm_add_le_max a b).trans (max_le ha hb)

end Ultrametric

section CoeffSum

variable (c : ℕ → ℕ) (q : K)


@[simp] theorem term_zero : term c q 0 = 0 := by simp [term]

theorem term_one : term c q 1 = (c 1 : K) * (q / (1 - q)) := by simp [term]

variable {q}

theorem nnnorm_term_le (hq : ‖q‖₊ < 1) (n : ℕ) : ‖term c q n‖₊ ≤ ‖q‖₊ ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hqn : ‖q ^ n‖₊ < 1 := by
    rw [nnnorm_pow]
    exact pow_lt_one₀ zero_le hq hn.ne'
  calc ‖term c q n‖₊ = ‖(c n : K)‖₊ * (‖q ^ n‖₊ / ‖1 - q ^ n‖₊) := by
        rw [term, nnnorm_mul, nnnorm_div]
    _ = ‖(c n : K)‖₊ * ‖q‖₊ ^ n := by rw [nnnorm_one_sub_of_lt_one hqn, div_one, nnnorm_pow]
    _ ≤ 1 * ‖q‖₊ ^ n := by
        gcongr
        exact nnnorm_natCast_le_one K (c n)
    _ = ‖q‖₊ ^ n := one_mul _

theorem nnnorm_term_le_nnnorm (hq : ‖q‖₊ < 1) (n : ℕ) : ‖term c q n‖₊ ≤ ‖q‖₊ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  calc ‖term c q n‖₊ ≤ ‖q‖₊ ^ n := nnnorm_term_le c hq n
    _ ≤ ‖q‖₊ ^ 1 := pow_le_pow_of_le_one zero_le hq.le hn
    _ = ‖q‖₊ := pow_one _

variable [CompleteSpace K]

theorem tendsto_term (hq : ‖q‖₊ < 1) :
    Tendsto (term c q) cofinite (nhds 0) := by
  rw [Nat.cofinite_eq_atTop]
  refine squeeze_zero_norm (fun n => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) ?_)
  · exact_mod_cast nnnorm_term_le c hq n
  · exact_mod_cast hq

theorem summable_term (hq : ‖q‖₊ < 1) : Summable (term c q) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (tendsto_term c hq)


theorem nnnorm_coeffSum_le (hq : ‖q‖₊ < 1) : ‖coeffSum c q‖₊ ≤ ‖q‖₊ :=
  nnnorm_tsum_le_of_forall_le (nnnorm_term_le_nnnorm c hq)

theorem nnnorm_coeffSum_sub_le (hq : ‖q‖₊ < 1) :
    ‖coeffSum c q - (c 1 : K) * q‖₊ ≤ ‖q‖₊ ^ 2 := by
  have hq1 : (1 : K) - q ≠ 0 := one_sub_ne_zero_of_lt_one hq

  have hsplit : coeffSum c q = term c q 1 + ∑' n, ite (n = 1) 0 (term c q n) :=
    (summable_term c hq).tsum_eq_add_tsum_ite 1

  have htail : ‖∑' n, ite (n = 1) 0 (term c q n)‖₊ ≤ ‖q‖₊ ^ 2 := by
    refine nnnorm_tsum_le_of_forall_le fun n => ?_
    rcases eq_or_ne n 1 with rfl | hn
    · simp
    rw [if_neg hn]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp

    have h2n : 2 ≤ n := by omega
    calc ‖term c q n‖₊ ≤ ‖q‖₊ ^ n := nnnorm_term_le c hq n
      _ ≤ ‖q‖₊ ^ 2 := pow_le_pow_of_le_one zero_le hq.le h2n

  have hlead : ‖term c q 1 - (c 1 : K) * q‖₊ ≤ ‖q‖₊ ^ 2 := by
    have hkey : term c q 1 - (c 1 : K) * q = (c 1 : K) * (q ^ 2 / (1 - q)) := by
      rw [term_one]
      field_simp
      ring
    rw [hkey, nnnorm_mul, nnnorm_div, nnnorm_one_sub_of_lt_one hq, div_one, nnnorm_pow]
    calc ‖(c 1 : K)‖₊ * ‖q‖₊ ^ 2 ≤ 1 * ‖q‖₊ ^ 2 := by
          gcongr
          exact nnnorm_natCast_le_one K (c 1)
      _ = ‖q‖₊ ^ 2 := one_mul _

  calc ‖coeffSum c q - (c 1 : K) * q‖₊
      = ‖(term c q 1 - (c 1 : K) * q) + ∑' n, ite (n = 1) 0 (term c q n)‖₊ := by
        rw [hsplit]; ring_nf
    _ ≤ ‖q‖₊ ^ 2 := nnnorm_add_le_of_le hlead htail

end CoeffSum

section Coefficients

variable [CompleteSpace K]


theorem twelve_dvd (n : ℕ) : 12 ∣ 5 * n ^ 3 + 7 * n ^ 5 := by
  have : ((5 * n ^ 3 + 7 * n ^ 5 : ℕ) : ZMod 12) = 0 := by
    push_cast
    generalize (n : ZMod 12) = x
    revert x
    decide
  exact (ZMod.natCast_eq_zero_iff _ _).mp this

theorem b_mul_twelve (n : ℕ) : b n * 12 = 5 * n ^ 3 + 7 * n ^ 5 :=
  Nat.div_mul_cancel (twelve_dvd n)

@[simp] theorem b_one : b 1 = 1 := by norm_num [b]

variable (q : K)


variable {q}

theorem nnnorm_a₄_le (hq : ‖q‖₊ < 1) : ‖a₄ q‖₊ ≤ ‖q‖₊ := by
  rw [a₄, nnnorm_neg]
  exact nnnorm_coeffSum_le _ hq

theorem nnnorm_a₆_le (hq : ‖q‖₊ < 1) : ‖a₆ q‖₊ ≤ ‖q‖₊ := by
  rw [a₆, nnnorm_neg]
  exact nnnorm_coeffSum_le _ hq

theorem nnnorm_a₄_add_five_mul_le (hq : ‖q‖₊ < 1) : ‖a₄ q + 5 * q‖₊ ≤ ‖q‖₊ ^ 2 := by
  have h := nnnorm_coeffSum_sub_le (K := K) (fun n => 5 * n ^ 3) hq
  have h5 : (((fun n => 5 * n ^ 3) 1 : ℕ) : K) = 5 := by norm_num
  rw [h5] at h
  calc ‖a₄ q + 5 * q‖₊ = ‖-(coeffSum (fun n => 5 * n ^ 3) q - 5 * q)‖₊ := by
        rw [a₄]; congr 1; ring
    _ = ‖coeffSum (fun n => 5 * n ^ 3) q - 5 * q‖₊ := nnnorm_neg _
    _ ≤ ‖q‖₊ ^ 2 := h

theorem nnnorm_a₆_add_le (hq : ‖q‖₊ < 1) : ‖a₆ q + q‖₊ ≤ ‖q‖₊ ^ 2 := by
  have h := nnnorm_coeffSum_sub_le (K := K) b hq
  rw [b_one, Nat.cast_one, one_mul] at h
  calc ‖a₆ q + q‖₊ = ‖-(coeffSum b q - q)‖₊ := by congr 1; rw [a₆]; ring
    _ = ‖coeffSum b q - q‖₊ := nnnorm_neg _
    _ ≤ ‖q‖₊ ^ 2 := h

end Coefficients

section Curve

variable (q : K)


@[simp] theorem curve_a₁ : (curve q).a₁ = 1 := rfl
@[simp] theorem curve_a₂ : (curve q).a₂ = 0 := rfl
@[simp] theorem curve_a₃ : (curve q).a₃ = 0 := rfl
@[simp] theorem curve_a₄ : (curve q).a₄ = a₄ q := rfl
@[simp] theorem curve_a₆ : (curve q).a₆ = a₆ q := rfl

theorem curve_Δ :
    (curve q).Δ = -a₆ q + a₄ q ^ 2 - 64 * a₄ q ^ 3 - 432 * a₆ q ^ 2 + 72 * a₄ q * a₆ q := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curve_a₁, curve_a₂, curve_a₃, curve_a₄, curve_a₆]
  ring

theorem curve_c₄ : (curve q).c₄ = 1 - 48 * a₄ q := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, curve_a₁, curve_a₂,
    curve_a₃, curve_a₄]
  ring

end Curve

end TateCurve
