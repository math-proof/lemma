import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.RingTheory.PowerSeries.ExpLog.Part6
import Lemma.PowerSeries.InfiniteProducts
open PowerSeries
open Finset
open scoped PowerSeries BigOperators


section
-- ac-theorems


namespace PowerSeries

open Nat Finset

variable (K : Type*) [CommRing K] [Algebra ℚ K]

variable {K}


@[simp]
lemma coeff_expbar (n : ℕ) :
    coeff n (expbar K) = if n = 0 then 0 else algebraMap ℚ K (1 / n !) := by
  simp only [expbar, map_sub, coeff_exp]
  rcases n with _ | n
  · simp
  · simp

@[simp]
lemma constantCoeff_expbar : constantCoeff (expbar K) = 0 := by
  simp [expbar]

lemma expbar_eq_exp_sub_one : expbar K = exp K - 1 := rfl


/-- The first few coefficients of `exp`: [x⁰]exp = 1, [x¹]exp = 1. -/
@[simp] lemma coeff_exp_zero : coeff 0 (exp K) = 1 := by simp [coeff_exp]
@[simp] lemma coeff_exp_one : coeff 1 (exp K) = 1 := by simp [coeff_exp]

/-- The first few coefficients of `logbar`: [x⁰]logbar = 0, [x¹]logbar = 1. -/
@[simp] lemma coeff_logbar_zero : coeff 0 (logbar K) = 0 := by simp [coeff_logbar]
@[simp] lemma coeff_logbar_one : coeff 1 (logbar K) = 1 := by simp [coeff_logbar]

/-- The first few coefficients of `expbar`: [x⁰]expbar = 0, [x¹]expbar = 1. -/
@[simp] lemma coeff_expbar_zero : coeff 0 (expbar K) = 0 := by simp [coeff_expbar]
@[simp] lemma coeff_expbar_one : coeff 1 (expbar K) = 1 := by simp [coeff_expbar]

/-- The `logbar` series can be expressed as `x - x²/2 + x³/3 - x⁴/4 + ...`. -/
lemma logbar_eq_sum_alternating : logbar K = mk fun n =>
    if n = 0 then 0 else algebraMap ℚ K ((-1 : ℚ) ^ (n - 1) / n) := rfl

/-- `exp` has constant term 1. This is part of Definition 7.8.2 (def.fps.exp-log). -/
lemma exp_constantCoeff : constantCoeff (exp K) = 1 := constantCoeff_exp

/-- `logbar` has constant term 0. This is part of Definition 7.8.2 (def.fps.exp-log). -/
lemma logbar_constantCoeff : constantCoeff (logbar K) = 0 := constantCoeff_logbar

/-- `expbar` has constant term 0. This is part of Definition 7.8.2 (def.fps.exp-log). -/
lemma expbar_constantCoeff : constantCoeff (expbar K) = 0 := constantCoeff_expbar

/-- The relationship between `exp` and `expbar`: `exp = 1 + expbar`. -/
lemma exp_eq_one_add_expbar : exp K = 1 + expbar K := by
  simp only [expbar]
  ring


variable (K) in

@[simp]
lemma coeff_invOnePlusX (n : ℕ) :
    coeff n (invOnePlusX K) = algebraMap ℚ K ((-1 : ℚ) ^ n) :=
  coeff_mk _ _

/-- The derivative of `logbar` is `invOnePlusX`. This is part of the proof of
Proposition 7.8.3 (prop.fps.exp-log-der). -/
lemma derivative_logbar : d⁄dX (logbar K) = invOnePlusX K := by
  ext n
  rw [coeff_derivative, coeff_logbar, coeff_invOnePlusX]
  simp only [add_eq_zero, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
  have h1 : (↑n + 1 : K) = algebraMap ℚ K (↑n + 1) := by simp
  have h2 : (↑n + 1 : ℚ) = (↑(n + 1) : ℚ) := by simp
  rw [h1, ← h2, ← map_mul]
  congr 1
  field_simp

/-- The derivative of `expbar` equals `exp`. This is equation (7.8.3) in the proof of
Proposition 7.8.3 (prop.fps.exp-log-der). -/
lemma derivative_expbar : d⁄dX (expbar K) = exp K := by
  unfold expbar
  simp [map_sub, derivative_exp]

/-- Chain rule for composition with `exp`: `(exp ∘ g)' = (exp ∘ g) · g'`.
This is Proposition 7.8.3(a) (prop.fps.exp-log-der). -/
lemma derivative_exp_comp {g : K⟦X⟧} (hg : constantCoeff g = 0) :
    d⁄dX ((exp K).subst g) = (exp K).subst g * d⁄dX g := by
  have hsub : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  rw [derivative_subst (f := exp K) hsub, derivative_exp]

/-- Chain rule for composition with `expbar`: `(expbar ∘ g)' = (exp ∘ g) · g'`.
This is Proposition 7.8.3(a) (prop.fps.exp-log-der).

Note that `expbar = exp - 1`, so `expbar' = exp' = exp`, and the chain rule gives
`(expbar ∘ g)' = (exp ∘ g) · g'`. -/
lemma derivative_expbar_comp {g : K⟦X⟧} (hg : constantCoeff g = 0) :
    d⁄dX ((expbar K).subst g) = (exp K).subst g * d⁄dX g := by
  have hsub : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  rw [derivative_subst (f := expbar K) hsub, derivative_expbar]

section FieldLemmas

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- `invOnePlusX K * (1 + X) = 1`. -/
lemma invOnePlusX_mul_one_add_X : invOnePlusX K * (1 + X) = 1 := by
  ext n
  simp only [coeff_mul, coeff_one]
  rcases n with _ | n
  · simp only [Finset.Nat.antidiagonal_zero, sum_singleton]
    simp only [invOnePlusX, coeff_mk, pow_zero, map_one]
    simp only [map_add, coeff_one, ite_true, coeff_X]
    norm_num
  · simp only [ite_false, Nat.succ_ne_zero]
    rw [Nat.sum_antidiagonal_succ']
    simp only [invOnePlusX, coeff_mk, map_add, coeff_one, coeff_X]
    simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add]
    have hsimp : ∀ x ∈ HasAntidiagonal.antidiagonal n,
        (algebraMap ℚ K) ((-1) ^ x.1) * (if x.2 + 1 = 1 then 1 else 0) =
        if x.2 = 0 then (algebraMap ℚ K) ((-1) ^ x.1) else 0 := by
      intro ⟨i, j⟩ _
      by_cases hj : j = 0
      · simp [hj]
      · have hne : j + 1 ≠ 1 := by omega
        simp only [hne, ite_false, mul_zero, hj]
    rw [sum_congr rfl hsimp]
    have hsum : ∑ x ∈ HasAntidiagonal.antidiagonal n, (if x.2 = 0 then (algebraMap ℚ K) ((-1 : ℚ) ^ x.1) else 0) =
                (algebraMap ℚ K) ((-1 : ℚ) ^ n) := by
      rw [← sum_filter]
      have hfilter : filter (fun x => x.2 = 0) (HasAntidiagonal.antidiagonal n) = {(n, 0)} := by
        ext ⟨i, j⟩
        simp only [mem_filter, HasAntidiagonal.mem_antidiagonal, mem_singleton, Prod.mk.injEq]
        constructor
        · rintro ⟨hij, rfl⟩
          simp at hij
          exact ⟨hij, rfl⟩
        · rintro ⟨rfl, rfl⟩
          simp
      rw [hfilter, sum_singleton]
    rw [hsum]
    simp only [pow_succ, mul_neg_one, map_neg]
    norm_num

/-- `(invOnePlusX K).subst g = (1 + g)⁻¹` when `constantCoeff g = 0`. -/
lemma invOnePlusX_subst_eq_inv {g : K⟦X⟧} (hg : constantCoeff g = 0) :
    (invOnePlusX K).subst g = (1 + g)⁻¹ := by
  have hsub : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  have h : (invOnePlusX K).subst g * (1 + g) = 1 := by
    have h1 : (1 + X : K⟦X⟧).subst g = 1 + g := by
      rw [subst_add hsub, subst_X hsub]
      congr 1
      rw [← coe_substAlgHom hsub]
      simp
    rw [← h1, ← subst_mul hsub, invOnePlusX_mul_one_add_X]
    rw [← coe_substAlgHom hsub]
    simp
  have hne : constantCoeff (1 + g) ≠ 0 := by simp [hg]
  symm
  rw [inv_eq_iff_mul_eq_one hne]
  exact h

/-- Chain rule for composition with `logbar`: `(logbar ∘ g)' = (1+g)⁻¹ · g'`.
This is Proposition 7.8.3(b) (prop.fps.exp-log-der).
Note: Requires Field K for the inverse to exist. -/
lemma derivative_logbar_comp {g : K⟦X⟧} (hg : constantCoeff g = 0) :
    d⁄dX ((logbar K).subst g) = (1 + g)⁻¹ * d⁄dX g := by
  have hsub : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  rw [derivative_subst (hg := hsub), derivative_logbar]
  congr 1
  exact invOnePlusX_subst_eq_inv hg

/-- `logbar ∘ expbar = x` for fields. This is the second part of Theorem 7.8.5 (thm.fps.exp-log-inv),
equation (7.8.1).

The proof strategy (from the textbook) is to show that `logbar ∘ expbar` and `X` have:
1. The same constant term (both are 0)
2. The same derivative (both equal 1)
Then by Theorem 7.3.7(h), they must be equal.

For the derivative calculation:
- `(logbar ∘ expbar)' = (logbar' ∘ expbar) · expbar'` by chain rule
- `logbar' = (1+X)⁻¹` and `expbar' = exp`
- `(1+X)⁻¹ ∘ expbar = (1 + expbar)⁻¹ = exp⁻¹` since `1 + expbar = exp`
- So `(logbar ∘ expbar)' = exp⁻¹ · exp = 1 = X'`

Note: This version is for fields. The general CommRing version is `logbar_comp_expbar`. -/
lemma logbar_comp_expbar' : (logbar K).subst (expbar K) = X := by
  have hexp0 : constantCoeff (expbar K) = 0 := constantCoeff_expbar
  have hlog0 : constantCoeff (logbar K) = 0 := constantCoeff_logbar
  have hsub : HasSubst (expbar K) := HasSubst.of_constantCoeff_zero' hexp0
  -- Use derivative.ext: show both have same constant term and same derivative
  apply derivative.ext (R := K)
  · -- Same derivative: both equal 1
    rw [derivative_subst (hg := hsub)]
    rw [derivative_logbar, derivative_expbar]
    -- Now: (invOnePlusX K).subst (expbar K) * exp K = 1
    -- Use invOnePlusX_subst_eq_inv: (invOnePlusX K).subst g = (1 + g)⁻¹
    rw [invOnePlusX_subst_eq_inv hexp0]
    -- Now: (1 + expbar K)⁻¹ * exp K = 1
    have hone_plus_expbar : 1 + expbar K = exp K := by simp [expbar]
    rw [hone_plus_expbar]
    have hexp_ne : constantCoeff (exp K : K⟦X⟧) ≠ 0 := by simp [constantCoeff_exp]
    rw [MvPowerSeries.inv_mul_cancel _ hexp_ne]
    simp
  · -- Same constant term: both are 0
    have h1 : MvPowerSeries.constantCoeff (σ := Unit) ((logbar K).subst (expbar K)) = 0 :=
      constantCoeff_subst_eq_zero hexp0 (logbar K) hlog0
    show MvPowerSeries.constantCoeff ((logbar K).subst (expbar K)) =
         MvPowerSeries.constantCoeff (X : K⟦X⟧)
    rw [h1]
    exact constantCoeff_X.symm

end FieldLemmas

/-- `invOnePlusX K * (1 + X) = 1` (for CommRing with Algebra ℚ, not just Field). -/
lemma invOnePlusX_mul_one_add_X' : invOnePlusX K * (1 + X) = 1 := by
  ext n
  simp only [coeff_mul, coeff_one]
  rcases n with _ | n
  · simp only [Finset.Nat.antidiagonal_zero, sum_singleton]
    simp only [invOnePlusX, coeff_mk, pow_zero, map_one]
    simp only [map_add, coeff_one, ite_true, coeff_X]
    norm_num
  · simp only [ite_false, Nat.succ_ne_zero]
    rw [Nat.sum_antidiagonal_succ']
    simp only [invOnePlusX, coeff_mk, map_add, coeff_one, coeff_X]
    simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add]
    have hsimp : ∀ x ∈ HasAntidiagonal.antidiagonal n,
        (algebraMap ℚ K) ((-1) ^ x.1) * (if x.2 + 1 = 1 then 1 else 0) =
        if x.2 = 0 then (algebraMap ℚ K) ((-1) ^ x.1) else 0 := by
      intro ⟨i, j⟩ _
      by_cases hj : j = 0
      · simp [hj]
      · have hne : j + 1 ≠ 1 := by omega
        simp only [hne, ite_false, mul_zero, hj]
    rw [sum_congr rfl hsimp]
    have hsum : ∑ x ∈ HasAntidiagonal.antidiagonal n, (if x.2 = 0 then (algebraMap ℚ K) ((-1 : ℚ) ^ x.1) else 0) =
                (algebraMap ℚ K) ((-1 : ℚ) ^ n) := by
      rw [← sum_filter]
      have hfilter : filter (fun x => x.2 = 0) (HasAntidiagonal.antidiagonal n) = {(n, 0)} := by
        ext ⟨i, j⟩
        simp only [mem_filter, HasAntidiagonal.mem_antidiagonal, mem_singleton, Prod.mk.injEq]
        constructor
        · rintro ⟨hij, rfl⟩
          simp at hij
          exact ⟨hij, rfl⟩
        · rintro ⟨rfl, rfl⟩
          simp
      rw [hfilter, sum_singleton]
    rw [hsum]
    simp only [pow_succ, mul_neg_one, map_neg]
    norm_num

/-- `(1 + X) * invOnePlusX K = 1` (for CommRing with Algebra ℚ). -/
lemma one_add_X_mul_invOnePlusX' : (1 + X) * invOnePlusX K = 1 := by
  rw [mul_comm, invOnePlusX_mul_one_add_X']

/-- Uniqueness lemma for ODEs of the form `h' = (1 + h) * g` with matching initial conditions.
This is used to prove `expbar_comp_logbar`. -/
lemma eq_of_derivative_eq_mul_of_inv
    {h₁ h₂ g : K⟦X⟧}
    (hd₁ : d⁄dX h₁ = (1 + h₁) * g) (hd₂ : d⁄dX h₂ = (1 + h₂) * g)
    (hc : constantCoeff h₁ = constantCoeff h₂) : h₁ = h₂ := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · have h1 : coeff 0 h₁ = constantCoeff h₁ := coeff_zero_eq_constantCoeff_apply h₁
      have h2 : coeff 0 h₂ = constantCoeff h₂ := coeff_zero_eq_constantCoeff_apply h₂
      rw [h1, h2, hc]
    · -- From h' = (1 + h) * g, we get coeff n (h') = coeff n ((1 + h) * g)
      have eq1 : coeff n (d⁄dX h₁) = coeff n ((1 + h₁) * g) := congrArg (coeff n) hd₁
      have eq2 : coeff n (d⁄dX h₂) = coeff n ((1 + h₂) * g) := congrArg (coeff n) hd₂
      rw [coeff_derivative] at eq1 eq2
      -- Show coeff n ((1 + h₁) * g) = coeff n ((1 + h₂) * g) using IH
      have h_eq : coeff n ((1 + h₁) * g) = coeff n ((1 + h₂) * g) := by
        simp only [add_mul, one_mul, map_add]
        congr 1
        simp only [coeff_mul]
        apply Finset.sum_congr rfl
        intro ⟨i, j⟩ hij
        simp only [HasAntidiagonal.mem_antidiagonal] at hij
        have hi : i ≤ n := by omega
        congr 1
        exact ih i (Nat.lt_succ_of_le hi)
      have h : coeff (n + 1) h₁ * (n + 1) = coeff (n + 1) h₂ * (n + 1) := by
        rw [eq1, eq2, h_eq]
      have hn1_ne : (n + 1 : ℚ) ≠ 0 := Nat.cast_add_one_ne_zero n
      have h' : coeff (n + 1) h₁ * (n + 1) * algebraMap ℚ K ((n + 1 : ℚ)⁻¹) =
                coeff (n + 1) h₂ * (n + 1) * algebraMap ℚ K ((n + 1 : ℚ)⁻¹) := by rw [h]
      have hcast : (n + 1 : K) = algebraMap ℚ K (n + 1 : ℚ) := by
        simp only [map_natCast, map_add, map_one]
      rw [hcast] at h'
      have hcancel : ∀ x : K, x * algebraMap ℚ K (n + 1 : ℚ) * algebraMap ℚ K ((n + 1 : ℚ)⁻¹) = x := by
        intro x
        rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hn1_ne, map_one, mul_one]
      rw [hcancel, hcancel] at h'
      exact h'

/-- `expbar ∘ logbar = x`. This is the first part of Theorem 7.8.5 (thm.fps.exp-log-inv),
equation (7.8.1).

The proof uses the uniqueness of solutions to ODEs: both `expbar ∘ logbar` and `X` satisfy
the ODE `h' = (1 + h) * invOnePlusX` with initial condition `h(0) = 0`. -/
lemma expbar_comp_logbar : (expbar K).subst (logbar K) = X := by
  have hlogbar : constantCoeff (logbar K) = 0 := constantCoeff_logbar
  have hsub : HasSubst (logbar K) := HasSubst.of_constantCoeff_zero' hlogbar
  apply eq_of_derivative_eq_mul_of_inv (g := invOnePlusX K)
  · -- (expbar ∘ logbar)' = (1 + expbar ∘ logbar) * invOnePlusX
    -- By chain rule: (expbar ∘ logbar)' = (exp ∘ logbar) * logbar'
    rw [derivative_expbar_comp hlogbar]
    -- exp ∘ logbar = (1 + expbar) ∘ logbar = 1 + expbar ∘ logbar
    have h1 : (exp K).subst (logbar K) = 1 + (expbar K).subst (logbar K) := by
      rw [exp_eq_one_add_expbar, subst_add hsub]
      congr 1
      rw [← coe_substAlgHom hsub, map_one]
    rw [h1, derivative_logbar]
  · -- X' = 1 = (1 + X) * invOnePlusX
    rw [derivative_X, one_add_X_mul_invOnePlusX']
  · -- constant terms are both 0
    rw [constantCoeff_subst_eq_apply hlogbar, constantCoeff_expbar, constantCoeff_X]

/-- `(invOnePlusX K).subst (expbar K) * exp K = 1`. This is a key lemma for proving
`logbar_comp_expbar`. -/
lemma invOnePlusX_subst_expbar_mul_exp : (invOnePlusX K).subst (expbar K) * exp K = 1 := by
  have hexp0 : constantCoeff (expbar K) = 0 := constantCoeff_expbar
  have hsub : HasSubst (expbar K) := HasSubst.of_constantCoeff_zero' hexp0
  have h1 : (invOnePlusX K * (1 + X)).subst (expbar K) = (1 : K⟦X⟧).subst (expbar K) := by
    rw [invOnePlusX_mul_one_add_X']
  rw [subst_mul hsub] at h1
  have h2 : (1 + X : K⟦X⟧).subst (expbar K) = exp K := by
    rw [subst_add hsub, subst_X hsub]
    rw [← coe_substAlgHom hsub, map_one]
    rw [exp_eq_one_add_expbar]
  have h3 : (1 : K⟦X⟧).subst (expbar K) = 1 := by
    rw [← coe_substAlgHom hsub, map_one]
  rw [h2, h3] at h1
  exact h1

/-- Uniqueness lemma for ODEs of the form `h' = 1` (constant) with matching initial conditions. -/
lemma eq_of_derivative_eq_one {h₁ h₂ : K⟦X⟧}
    (hd₁ : d⁄dX h₁ = 1) (hd₂ : d⁄dX h₂ = 1)
    (hc : constantCoeff h₁ = constantCoeff h₂) : h₁ = h₂ := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · have h1 : coeff 0 h₁ = constantCoeff h₁ := coeff_zero_eq_constantCoeff_apply h₁
      have h2 : coeff 0 h₂ = constantCoeff h₂ := coeff_zero_eq_constantCoeff_apply h₂
      rw [h1, h2, hc]
    · have eq1 : coeff n (d⁄dX h₁) = coeff n (1 : K⟦X⟧) := congrArg (coeff n) hd₁
      have eq2 : coeff n (d⁄dX h₂) = coeff n (1 : K⟦X⟧) := congrArg (coeff n) hd₂
      rw [coeff_derivative] at eq1 eq2
      have h : coeff (n + 1) h₁ * (n + 1) = coeff (n + 1) h₂ * (n + 1) := by
        rw [eq1, eq2]
      have hn1_ne : (n + 1 : ℚ) ≠ 0 := Nat.cast_add_one_ne_zero n
      have h' : coeff (n + 1) h₁ * (n + 1) * algebraMap ℚ K ((n + 1 : ℚ)⁻¹) =
                coeff (n + 1) h₂ * (n + 1) * algebraMap ℚ K ((n + 1 : ℚ)⁻¹) := by rw [h]
      have hcast : (n + 1 : K) = algebraMap ℚ K (n + 1 : ℚ) := by simp
      rw [hcast] at h'
      have hcancel : ∀ x : K, x * algebraMap ℚ K (n + 1 : ℚ) * algebraMap ℚ K ((n + 1 : ℚ)⁻¹) = x := by
        intro x
        rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hn1_ne, map_one, mul_one]
      rw [hcancel, hcancel] at h'
      exact h'

/-- `logbar ∘ expbar = x`. This is the second part of Theorem 7.8.5 (thm.fps.exp-log-inv),
equation (7.8.1).

The proof uses the uniqueness of solutions to ODEs: both `logbar ∘ expbar` and `X` satisfy
the ODE `h' = 1` with initial condition `h(0) = 0`. The key calculation is:
- `(logbar ∘ expbar)' = (logbar' ∘ expbar) · expbar'` by chain rule
- `logbar' = invOnePlusX` and `expbar' = exp`
- `(invOnePlusX ∘ expbar) · exp = 1` since `invOnePlusX · (1 + X) = 1` and `1 + expbar = exp`
- So `(logbar ∘ expbar)' = 1 = X'` -/
lemma logbar_comp_expbar : (logbar K).subst (expbar K) = X := by
  have hexp0 : constantCoeff (expbar K) = 0 := constantCoeff_expbar
  have hsub : HasSubst (expbar K) := HasSubst.of_constantCoeff_zero' hexp0
  -- Use ODE uniqueness: both satisfy h' = 1 with h(0) = 0
  apply eq_of_derivative_eq_one
  · -- (logbar ∘ expbar)' = 1
    rw [derivative_subst (hg := hsub), derivative_logbar, derivative_expbar]
    exact invOnePlusX_subst_expbar_mul_exp
  · simp
  · rw [constantCoeff_subst_eq_apply hexp0, constantCoeff_logbar, constantCoeff_X]


section PowerSeriesSets

variable {R : Type*} [CommRing R]

lemma X_mem_PowerSeries₀ : (X : R⟦X⟧) ∈ PowerSeries₀ := constantCoeff_X

lemma PowerSeries₀.sub_mem {f g : R⟦X⟧} (hf : f ∈ PowerSeries₀) (hg : g ∈ PowerSeries₀) :
    f - g ∈ PowerSeries₀ := by
  rw [mem_PowerSeries₀_iff, map_sub]
  rw [mem_PowerSeries₀_iff] at hf hg
  rw [hf, hg, sub_zero]

end PowerSeriesSets

section PowerSeriesSetsField

variable {R : Type*} [Field R]

lemma PowerSeries₁.inv_mem {f : R⟦X⟧} (hf : f ∈ PowerSeries₁) : f⁻¹ ∈ PowerSeries₁ := by
  rw [mem_PowerSeries₁_iff] at hf ⊢
  simp only [constantCoeff_inv, hf, inv_one]

/-- Division in `R⟦X⟧₁`: if `f, g ∈ R⟦X⟧₁`, then `f * g⁻¹ ∈ R⟦X⟧₁`.
This is part of Proposition 7.8.10(b) (prop.fps.Exp-Log-groups). -/
lemma PowerSeries₁.div_mem {f g : R⟦X⟧} (hf : f ∈ PowerSeries₁) (hg : g ∈ PowerSeries₁) :
    f * g⁻¹ ∈ PowerSeries₁ :=
  PowerSeries₁.mul_mem hf (PowerSeries₁.inv_mem hg)

end PowerSeriesSetsField

section ExpLogMaps

variable (K : Type*) [CommRing K] [Algebra ℚ K]

lemma expbar_mem_PowerSeries₀ : expbar K ∈ PowerSeries₀ := constantCoeff_expbar

variable {K}

lemma Exp_val (g : PowerSeries₀ (R := K)) : (Exp g).val = (exp K).subst g.val := rfl

lemma Log_val (f : PowerSeries₁ (R := K)) : (Log f).val = (logbar K).subst (f.val - 1) := rfl

/-- `Log (Exp g) = g` for any `g ∈ K⟦X⟧₀`. This is part of Lemma 7.8.8 (lem.fps.Exp-Log-maps-inv). -/
lemma Log_Exp (g : PowerSeries₀ (R := K)) : Log (Exp g) = g := by
  apply Subtype.ext
  simp only [Log_val, Exp_val]
  -- Need to show: (logbar K).subst ((exp K).subst g.val - 1) = g.val
  have hg : constantCoeff g.val = 0 := g.property
  have hsub_g : HasSubst g.val := HasSubst.of_constantCoeff_zero' hg
  have hsub_expbar : HasSubst (expbar K) := HasSubst.of_constantCoeff_zero' constantCoeff_expbar
  -- First, show (exp K).subst g.val - 1 = (expbar K).subst g.val using exp = 1 + expbar
  have h1 : (exp K).subst g.val - 1 = (expbar K).subst g.val := by
    rw [expbar]
    rw [← coe_substAlgHom hsub_g, map_sub, map_one, coe_substAlgHom]
  rw [h1]
  -- Use logbar_comp_expbar: (logbar K).subst (expbar K) = X
  -- and subst_comp_subst_apply: subst b (subst a f) = subst (subst b a) f
  -- With a = expbar K, b = g.val, f = logbar K:
  -- ((logbar K).subst (expbar K)).subst g.val = (logbar K).subst ((expbar K).subst g.val)
  rw [← subst_comp_subst_apply hsub_expbar hsub_g (logbar K)]
  rw [logbar_comp_expbar]
  rw [subst_X hsub_g]

lemma Exp_Log (f : PowerSeries₁ (R := K)) : Exp (Log f) = f := by
  apply Subtype.ext
  simp only [Exp, Log]
  -- First, establish that constantCoeff (f.val - 1) = 0
  have hf1 : constantCoeff (f.val - 1) = 0 := sub_one_mem_PowerSeries₀ f.property
  have hlogbar : constantCoeff (logbar K) = 0 := constantCoeff_logbar
  have h_logbar_subst : constantCoeff ((logbar K).subst (f.val - 1)) = 0 := by
    rw [constantCoeff_subst_eq_apply hf1, hlogbar]
  -- Show exp.subst g = expbar.subst g + 1
  have hsub_log : HasSubst ((logbar K).subst (f.val - 1)) :=
    HasSubst.of_constantCoeff_zero h_logbar_subst
  have exp_eq : (exp K).subst ((logbar K).subst (f.val - 1)) =
                (expbar K).subst ((logbar K).subst (f.val - 1)) + 1 := by
    have h : exp K = expbar K + 1 := by simp only [expbar, sub_add_cancel]
    rw [h, subst_add hsub_log, ← coe_substAlgHom hsub_log, map_one]
  rw [exp_eq]
  -- Use composition formula
  have hsub_fv1 : HasSubst (f.val - 1) := HasSubst.of_constantCoeff_zero hf1
  have hsub_logbar : HasSubst (logbar K) := HasSubst.of_constantCoeff_zero hlogbar
  have comp_eq : subst (subst (f.val - 1) (logbar K)) (expbar K) =
                 subst (f.val - 1) ((expbar K).subst (logbar K)) :=
    (subst_comp_subst_apply hsub_logbar hsub_fv1 (expbar K)).symm
  calc (expbar K).subst ((logbar K).subst (f.val - 1)) + 1
      = subst (subst (f.val - 1) (logbar K)) (expbar K) + 1 := by rfl
    _ = subst (f.val - 1) ((expbar K).subst (logbar K)) + 1 := by rw [comp_eq]
    _ = subst (f.val - 1) X + 1 := by rw [expbar_comp_logbar]
    _ = (f.val - 1) + 1 := by rw [subst_X hsub_fv1]
    _ = f.val := by ring

/-- `Exp` and `Log` are mutually inverse. This is Lemma 7.8.8 (lem.fps.Exp-Log-maps-inv). -/
lemma Exp_Log_inverse : Function.LeftInverse (Log (K := K)) Exp ∧
    Function.RightInverse (Log (K := K)) Exp :=
  ⟨Log_Exp, Exp_Log⟩


/-- Uniqueness lemma: if two power series satisfy the same first-order linear ODE
`h' = h * g` with the same initial condition, they are equal.
This is used to prove `Exp_add`. -/
lemma eq_of_derivative_eq_mul_self {h₁ h₂ g : K⟦X⟧}
    (hd₁ : d⁄dX h₁ = h₁ * g) (hd₂ : d⁄dX h₂ = h₂ * g)
    (hc : constantCoeff h₁ = constantCoeff h₂) : h₁ = h₂ := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · -- Base case: coefficient 0 equals constant coefficient
      have h1 : coeff 0 h₁ = constantCoeff h₁ := coeff_zero_eq_constantCoeff_apply h₁
      have h2 : coeff 0 h₂ = constantCoeff h₂ := coeff_zero_eq_constantCoeff_apply h₂
      rw [h1, h2, hc]
    · -- Inductive case: from h' = h * g, derive coeff (n+1) h * (n+1) = coeff n (h * g)
      have eq1 : coeff n (d⁄dX h₁) = coeff n (h₁ * g) := congrArg (coeff n) hd₁
      have eq2 : coeff n (d⁄dX h₂) = coeff n (h₂ * g) := congrArg (coeff n) hd₂
      rw [coeff_derivative] at eq1 eq2
      -- The convolution coeff n (h₁ * g) = coeff n (h₂ * g) by induction hypothesis
      have h_eq : coeff n (h₁ * g) = coeff n (h₂ * g) := by
        simp only [coeff_mul]
        apply Finset.sum_congr rfl
        intro ⟨i, j⟩ hij
        simp only [HasAntidiagonal.mem_antidiagonal] at hij
        have hi : i ≤ n := by omega
        congr 1
        exact ih i (Nat.lt_succ_of_le hi)
      -- Now coeff (n+1) h₁ * (n+1) = coeff (n+1) h₂ * (n+1)
      have h : coeff (n + 1) h₁ * (n + 1) = coeff (n + 1) h₂ * (n + 1) := by
        rw [eq1, eq2, h_eq]
      -- In a ℚ-algebra, we can cancel (n+1) by multiplying by its inverse
      have hn1_ne : (n + 1 : ℚ) ≠ 0 := Nat.cast_add_one_ne_zero n
      have h' : coeff (n + 1) h₁ * (n + 1) * algebraMap ℚ K ((n + 1 : ℚ)⁻¹) =
                coeff (n + 1) h₂ * (n + 1) * algebraMap ℚ K ((n + 1 : ℚ)⁻¹) := by rw [h]
      have hcast : (n + 1 : K) = algebraMap ℚ K (n + 1 : ℚ) := by simp
      rw [hcast] at h'
      have hcancel : ∀ x : K, x * algebraMap ℚ K (n + 1 : ℚ) * algebraMap ℚ K ((n + 1 : ℚ)⁻¹) = x := by
        intro x
        rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hn1_ne, map_one, mul_one]
      rw [hcancel, hcancel] at h'
      exact h'

/-- `Exp(f + g) = Exp(f) · Exp(g)`. This is Lemma 7.8.9(a) (lem.fps.Exp-Log-additive). -/
lemma Exp_add (f g : PowerSeries₀ (R := K)) :
    Exp (⟨f.val + g.val, by
      rw [mem_PowerSeries₀_iff, map_add, f.property, g.property, add_zero]⟩) =
    ⟨(Exp f).val * (Exp g).val, by
      rw [mem_PowerSeries₁_iff, map_mul, (Exp f).property, (Exp g).property, one_mul]⟩ := by
  -- Reduce to showing the underlying values are equal
  apply Subtype.ext
  simp only [Exp_val]
  -- Now need: (exp K).subst (f.val + g.val) = ((exp K).subst f.val) * ((exp K).subst g.val)
  have hf : constantCoeff f.val = 0 := f.property
  have hg : constantCoeff g.val = 0 := g.property
  have hsub_f : HasSubst f.val := HasSubst.of_constantCoeff_zero' hf
  have hsub_g : HasSubst g.val := HasSubst.of_constantCoeff_zero' hg
  have hsub_fg : HasSubst (f.val + g.val) := HasSubst.of_constantCoeff_zero' (by simp [hf, hg])
  -- Both sides satisfy the same ODE h' = h * (f' + g') with h(0) = 1
  apply eq_of_derivative_eq_mul_self
  · -- LHS: d/dX (exp.subst (f+g)) = exp.subst (f+g) * d/dX (f+g)
    rw [derivative_subst (f := exp K) (g := f.val + g.val) hsub_fg, derivative_exp]
  · -- RHS: d/dX (exp.subst f * exp.subst g) = (exp.subst f * exp.subst g) * d/dX (f+g)
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    rw [derivative_subst (f := exp K) (g := f.val) hsub_f, derivative_exp]
    rw [derivative_subst (f := exp K) (g := g.val) hsub_g, derivative_exp]
    simp only [map_add]
    ring
  · -- Constant coefficients both equal 1
    rw [map_mul]
    rw [constantCoeff_subst_eq_apply hf]
    rw [constantCoeff_subst_eq_apply hg]
    rw [constantCoeff_subst_eq_apply (by simp [hf, hg] : constantCoeff (f.val + g.val) = 0)]
    simp [constantCoeff_exp]

/-- `Log(fg) = Log(f) + Log(g)`. This is Lemma 7.8.9(b) (lem.fps.Exp-Log-additive). -/
lemma Log_mul (f g : PowerSeries₁ (R := K)) :
    Log (⟨f.val * g.val, by
      rw [mem_PowerSeries₁_iff, map_mul, f.property, g.property, one_mul]⟩) =
    ⟨(Log f).val + (Log g).val, by
      rw [mem_PowerSeries₀_iff, map_add, (Log f).property, (Log g).property, add_zero]⟩ := by
  -- The key insight: use Exp_Log and Log_Exp to show this is equivalent to Log(Exp(Log f + Log g))
  -- Step 1: f = Exp(Log f) and g = Exp(Log g)
  have hf : f = Exp (Log f) := (Exp_Log f).symm
  have hg : g = Exp (Log g) := (Exp_Log g).symm
  -- Step 2: Compute f.val * g.val in terms of Exp
  have hprod_val : f.val * g.val = (Exp (Log f)).val * (Exp (Log g)).val := by
    rw [← hf, ← hg]
  -- Step 3: By Exp_add, (Exp (Log f)).val * (Exp (Log g)).val = (Exp ⟨(Log f).val + (Log g).val, _⟩).val
  let sum_mem : (Log f).val + (Log g).val ∈ PowerSeries₀ :=
    PowerSeries₀.add_mem (Log f).property (Log g).property
  have hexp_add := Exp_add (Log f) (Log g)
  have hprod_eq_exp : (Exp (Log f)).val * (Exp (Log g)).val =
      (Exp ⟨(Log f).val + (Log g).val, sum_mem⟩).val := by
    exact (congrArg Subtype.val hexp_add).symm
  -- Step 4: Combine to get f.val * g.val = (Exp ⟨...⟩).val
  have hfg_val : f.val * g.val = (Exp ⟨(Log f).val + (Log g).val, sum_mem⟩).val := by
    rw [hprod_val, hprod_eq_exp]
  -- Step 5: Now we need to show Log ⟨f.val * g.val, _⟩ = ⟨(Log f).val + (Log g).val, _⟩
  -- Use Subtype.ext to reduce to showing the values are equal
  apply Subtype.ext
  simp only [Log_val]
  -- Goal: (logbar K).subst (f.val * g.val - 1) = (Log f).val + (Log g).val
  rw [hfg_val]
  -- Goal: (logbar K).subst ((Exp ⟨...⟩).val - 1) = (Log f).val + (Log g).val
  -- This is (Log (Exp ⟨...⟩)).val = (Log f).val + (Log g).val
  -- By Log_Exp, Log (Exp ⟨...⟩) = ⟨...⟩, so (Log (Exp ⟨...⟩)).val = (Log f).val + (Log g).val
  exact congrArg Subtype.val (Log_Exp ⟨(Log f).val + (Log g).val, sum_mem⟩)

/-- `Exp : (K⟦X⟧₀, +, 0) → (K⟦X⟧₁, ·, 1)` is a group homomorphism.
This is part of Theorem 7.8.11 (thm.fps.Exp-Log-group-iso). -/
lemma Exp_isAddGroupHom : ∀ f g : PowerSeries₀ (R := K),
    Exp (⟨f.val + g.val, PowerSeries₀.add_mem f.property g.property⟩) =
    ⟨(Exp f).val * (Exp g).val, PowerSeries₁.mul_mem (Exp f).property (Exp g).property⟩ := by
  intro f g
  exact Exp_add f g

/-- `Exp(0) = 1`. -/
lemma Exp_zero : Exp (⟨0, PowerSeries₀.zero_mem⟩ : PowerSeries₀ (R := K)) = 
    ⟨1, PowerSeries₁.one_mem⟩ := by
  apply Subtype.ext
  simp only [Exp_val]
  have hsub : HasSubst (0 : K⟦X⟧) := HasSubst.of_constantCoeff_zero' (by simp)
  ext n
  rw [coeff_subst' hsub]
  simp only [coeff_exp, smul_eq_mul, coeff_one]
  by_cases hn : n = 0
  · subst hn
    simp only [ite_true]
    have h : ∀ d : ℕ, algebraMap ℚ K (1 / ↑d.factorial) * coeff 0 ((0 : K⟦X⟧) ^ d) = 
             if d = 0 then 1 else 0 := by
      intro d
      by_cases hd : d = 0
      · simp [hd]
      · simp [hd, zero_pow hd]
    rw [finsum_eq_single _ 0 (fun d hd => by simp [hd])]
    simp
  · simp only [hn, ite_false]
    rw [finsum_eq_zero_of_forall_eq_zero]
    intro d
    by_cases hd : d = 0
    · simp [hd, hn]
    · simp [zero_pow hd]

/-- `Log(1) = 0`. -/
lemma Log_one : Log (⟨1, PowerSeries₁.one_mem⟩ : PowerSeries₁ (R := K)) = 
    ⟨0, PowerSeries₀.zero_mem⟩ := by
  apply Subtype.ext
  simp only [Log_val]
  have h : (1 : K⟦X⟧) - 1 = 0 := sub_self 1
  rw [h]
  have hsub : HasSubst (0 : K⟦X⟧) := HasSubst.of_constantCoeff_zero' (by simp)
  ext n
  rw [coeff_subst' hsub]
  simp only [coeff_logbar, smul_eq_mul, map_zero]
  rw [finsum_eq_zero_of_forall_eq_zero]
  intro d
  by_cases hd : d = 0
  · simp [hd]
  · simp [zero_pow hd]

/-- **Theorem 7.8.11** (thm.fps.Exp-Log-group-iso): The maps `Exp` and `Log` are mutually inverse
group isomorphisms between `(K⟦X⟧₀, +, 0)` and `(K⟦X⟧₁, ·, 1)`.

This means:
1. `Exp` is a bijection with inverse `Log`
2. `Exp(f + g) = Exp(f) · Exp(g)` for all `f, g ∈ K⟦X⟧₀`
3. `Exp(0) = 1`

Equivalently:
1. `Log` is a bijection with inverse `Exp`
2. `Log(f · g) = Log(f) + Log(g)` for all `f, g ∈ K⟦X⟧₁`
3. `Log(1) = 0`

The proof combines:
- `Log_Exp` and `Exp_Log`: mutual inverse property (Lemma 7.8.8)
- `Exp_add`: Exp preserves addition→multiplication (Lemma 7.8.9(a))
- `Log_mul`: Log preserves multiplication→addition (Lemma 7.8.9(b))
-/
lemma Exp_Log_groupIso : 
    -- Part 1: Exp and Log are mutual inverses
    (Function.LeftInverse (Log (K := K)) Exp ∧ Function.RightInverse (Log (K := K)) Exp) ∧
    -- Part 2: Exp is a group homomorphism (addition → multiplication)
    (∀ f g : PowerSeries₀ (R := K), 
      Exp ⟨f.val + g.val, PowerSeries₀.add_mem f.property g.property⟩ = 
      ⟨(Exp f).val * (Exp g).val, PowerSeries₁.mul_mem (Exp f).property (Exp g).property⟩) ∧
    -- Part 3: Exp maps identity to identity
    (Exp (⟨0, PowerSeries₀.zero_mem⟩ : PowerSeries₀ (R := K)) = ⟨1, PowerSeries₁.one_mem⟩) := by
  refine ⟨⟨Log_Exp, Exp_Log⟩, Exp_isAddGroupHom, Exp_zero⟩

end ExpLogMaps


section LogarithmicDerivative

variable {R : Type*} [Field R]

/-- The definition of the logarithmic derivative: `loder f = f' * f⁻¹`. -/
lemma loder_def (f : R⟦X⟧) : loder f = d⁄dX f * f⁻¹ := rfl


/-- An FPS with constant term 1 is invertible (a unit).
This is the well-definedness statement for `loder` in Definition 7.8.12 (def.fps.loder.1).

The proof: If `constantCoeff f = 1`, then `constantCoeff f` is a unit in `R`, so by
Proposition prop.fps.invertible, `f` is invertible in `R⟦X⟧`. -/
lemma isUnit_of_constantCoeff_eq_one {f : R⟦X⟧} (hf : constantCoeff f = 1) : IsUnit f := by
  rw [isUnit_iff_exists_inv]
  use f⁻¹
  have h : constantCoeff f ≠ 0 := by simp [hf]
  exact PowerSeries.mul_inv_cancel f h

/-- An FPS is invertible iff its constant coefficient is a unit.
This is a more general version of `isUnit_of_constantCoeff_eq_one`. -/
lemma isUnit_iff_constantCoeff_isUnit {f : R⟦X⟧} : IsUnit f ↔ IsUnit (constantCoeff f) := by
  constructor
  · intro h
    exact h.map constantCoeff
  · intro h
    rw [isUnit_iff_exists_inv]
    use f⁻¹
    have h' : constantCoeff f ≠ 0 := h.ne_zero
    exact PowerSeries.mul_inv_cancel f h'

/-- For FPS with constant term 1, we have `f * f⁻¹ = 1`.
This is a key property used in the definition of `loder`. -/
lemma mul_inv_cancel_of_constantCoeff_eq_one {f : R⟦X⟧} (hf : constantCoeff f = 1) :
    f * f⁻¹ = 1 := by
  have h : constantCoeff f ≠ 0 := by simp [hf]
  exact PowerSeries.mul_inv_cancel f h

/-- For FPS with constant term 1, we have `f⁻¹ * f = 1`. -/
lemma inv_mul_cancel_of_constantCoeff_eq_one {f : R⟦X⟧} (hf : constantCoeff f = 1) :
    f⁻¹ * f = 1 := by
  have h : constantCoeff f ≠ 0 := by simp [hf]
  exact PowerSeries.inv_mul_cancel f h

/-- The inverse of an FPS with constant term 1 also has constant term 1. -/
lemma constantCoeff_inv_of_constantCoeff_eq_one {f : R⟦X⟧} (hf : constantCoeff f = 1) :
    constantCoeff f⁻¹ = 1 := by
  simp [constantCoeff_inv, hf]

/-- The series `invOnePlusX` equals `(1 + X)⁻¹`. -/
lemma invOnePlusX_eq_inv [Algebra ℚ R] : invOnePlusX R = (1 + X)⁻¹ := by
  have h : constantCoeff (1 + X : R⟦X⟧) ≠ 0 := by simp
  rw [eq_inv_iff_mul_eq_one h]
  ext n
  simp only [coeff_mul, coeff_one, map_add, coeff_X]
  cases n with
  | zero =>
    simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    simp [invOnePlusX, coeff_mk]
  | succ n =>
    simp only [invOnePlusX, coeff_mk, Nat.succ_ne_zero, ↓reduceIte]
    have h0 : (n + 1, 0) ∈ HasAntidiagonal.antidiagonal (n + 1) := by simp [HasAntidiagonal.mem_antidiagonal]
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem h0]
    simp only [↓reduceIte]
    have h1' : (n, 1) ∈ HasAntidiagonal.antidiagonal (n + 1) \ {(n + 1, 0)} := by
      simp [Finset.mem_sdiff, HasAntidiagonal.mem_antidiagonal, Finset.mem_singleton]
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem h1']
    simp only [Nat.add_one_ne_zero, ↓reduceIte, zero_add]
    have hrest : ∀ x ∈ (HasAntidiagonal.antidiagonal (n + 1) \ {(n + 1, 0)}) \ {(n, 1)},
        (algebraMap ℚ R) ((-1) ^ x.1) * ((if x.2 = 0 then 1 else 0) + if x.2 = 1 then 1 else 0) = 0 := by
      intro ⟨i, j⟩ hij
      simp only [Finset.mem_sdiff, HasAntidiagonal.mem_antidiagonal, Finset.mem_singleton,
                 Prod.mk.injEq, not_and] at hij
      have hij1 : i + j = n + 1 := hij.1.1
      have hij2 : i = n + 1 → ¬j = 0 := hij.1.2
      have hij4 : i = n → ¬j = 1 := hij.2
      have hj0 : j ≠ 0 := by
        intro hj0
        subst hj0
        simp at hij1
        exact hij2 hij1 rfl
      have hj1 : j ≠ 1 := by
        intro hj1
        subst hj1
        have : i = n := by omega
        exact hij4 this rfl
      simp only [hj0, hj1, ↓reduceIte, add_zero, mul_zero]
    rw [Finset.sum_eq_zero hrest]
    simp only [add_zero, mul_one]
    have h1 : (0 : ℕ) ≠ 1 := by omega
    simp only [h1, ↓reduceIte, add_zero, mul_one]
    have : ((-1 : ℚ) ^ (n + 1) : ℚ) + (-1) ^ n = 0 := by ring
    simp only [map_pow, map_neg, map_one]
    have h2 : ((-1 : R) ^ (n + 1) : R) + (-1) ^ n = 0 := by
      calc ((-1 : R) ^ (n + 1) : R) + (-1) ^ n
          = (algebraMap ℚ R) ((-1 : ℚ) ^ (n + 1)) + (algebraMap ℚ R) ((-1 : ℚ) ^ n) := by
            simp only [map_pow, map_neg, map_one]
          _ = (algebraMap ℚ R) ((-1 : ℚ) ^ (n + 1) + (-1) ^ n) := by rw [map_add]
          _ = (algebraMap ℚ R) 0 := by rw [this]
          _ = 0 := by simp
    exact h2

/-- Helper lemma: if `a * b = 1`, then `(a.subst g)⁻¹ = b.subst g`. -/
lemma subst_inv_of_mul_eq_one {g a b : R⟦X⟧} (hg : HasSubst g) (hab : a * b = 1) :
    (a.subst g)⁻¹ = b.subst g := by
  have h : a.subst g * b.subst g = 1 := by
    rw [← subst_mul hg, hab, ← coe_substAlgHom hg, map_one]
  have hcc : constantCoeff (a.subst g) ≠ 0 := by
    intro h0
    have : constantCoeff (a.subst g * b.subst g) = 0 := by simp [h0]
    rw [h] at this
    simp at this
  rw [eq_comm, MvPowerSeries.eq_inv_iff_mul_eq_one hcc, mul_comm, h]

/-- The logarithmic derivative equals the derivative of the logarithm over ℚ-algebras.
This is Proposition 7.8.13 (prop.fps.loder.log). -/
lemma loder_eq_derivative_Log [Algebra ℚ R] {f : R⟦X⟧} (hf : constantCoeff f = 1) :
    loder f = d⁄dX ((logbar R).subst (f - 1)) := by
  -- Need HasSubst for f - 1
  have hf1 : constantCoeff (f - 1) = 0 := by simp [hf]
  have hsub : HasSubst (f - 1) := HasSubst.of_constantCoeff_zero' hf1
  -- Use chain rule: d⁄dX ((logbar R).subst (f - 1)) = (d⁄dX (logbar R)).subst (f - 1) * d⁄dX (f - 1)
  rw [derivative_subst (f := logbar R) (g := f - 1) hsub]
  -- Apply derivative_logbar
  rw [derivative_logbar (K := R)]
  -- Apply invOnePlusX_eq_inv
  rw [invOnePlusX_eq_inv]
  -- Simplify derivative of (f - 1)
  have hderiv : d⁄dX (f - 1) = d⁄dX f := by simp
  rw [hderiv]
  -- Unfold loder and use commutativity
  rw [loder]
  rw [mul_comm]
  congr 1
  -- Need: (1 + X)⁻¹.subst (f - 1) = f⁻¹
  have hmul : (1 + X : R⟦X⟧) * (1 + X)⁻¹ = 1 := by
    have h : constantCoeff (1 + X : R⟦X⟧) ≠ 0 := by simp
    exact MvPowerSeries.mul_inv_cancel _ h
  have hinv := subst_inv_of_mul_eq_one hsub hmul
  rw [← hinv]
  -- Show (1 + X).subst (f - 1) = f
  have h1 : (1 + X : R⟦X⟧).subst (f - 1) = f := by
    rw [subst_add hsub, ← coe_substAlgHom hsub, map_one, substAlgHom_X hsub]
    ring
  rw [h1]

/-- The logarithmic derivative is additive under multiplication: `loder(fg) = loder(f) + loder(g)`.
This is Proposition 7.8.14 (prop.fps.loder.prod).

Note: This does NOT require `R` to be a ℚ-algebra. -/
lemma loder_mul {f g : R⟦X⟧} (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    loder (f * g) = loder f + loder g := by
  simp only [loder_def]
  -- Use Leibniz rule: d⁄dX (f * g) = f * d⁄dX g + g * d⁄dX f
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  -- Use (f * g)⁻¹ = g⁻¹ * f⁻¹
  rw [PowerSeries.mul_inv_rev]
  -- We need f * f⁻¹ = 1 and g * g⁻¹ = 1
  have hf' : f * f⁻¹ = 1 := PowerSeries.mul_inv_cancel f (by simp [hf])
  have hg' : g * g⁻¹ = 1 := PowerSeries.mul_inv_cancel g (by simp [hg])
  -- Compute: (f * d⁄dX g + g * d⁄dX f) * (g⁻¹ * f⁻¹)
  --        = f * f⁻¹ * d⁄dX g * g⁻¹ + g * g⁻¹ * d⁄dX f * f⁻¹
  --        = d⁄dX g * g⁻¹ + d⁄dX f * f⁻¹
  calc (f * d⁄dX g + g * d⁄dX f) * (g⁻¹ * f⁻¹)
      = f * f⁻¹ * (d⁄dX g * g⁻¹) + g * g⁻¹ * (d⁄dX f * f⁻¹) := by ring
    _ = 1 * (d⁄dX g * g⁻¹) + 1 * (d⁄dX f * f⁻¹) := by rw [hf', hg']
    _ = d⁄dX f * f⁻¹ + d⁄dX g * g⁻¹ := by ring

/-- The logarithmic derivative of a product of `k` FPSs.
This is Corollary 7.8.15 (cor.fps.loder.prodk).

Note: This does NOT require `R` to be a ℚ-algebra. -/
lemma loder_prod {ι : Type*} (s : Finset ι) (f : ι → R⟦X⟧)
    (hf : ∀ i ∈ s, constantCoeff (f i) = 1) :
    loder (∏ i ∈ s, f i) = ∑ i ∈ s, loder (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [loder_def]
  | cons a s ha ih =>
    rw [Finset.prod_cons ha, Finset.sum_cons ha]
    rw [loder_mul (hf _ (Finset.mem_cons_self a s))]
    · rw [ih (fun i hi => hf i (Finset.mem_cons_of_mem hi))]
    · rw [map_prod]
      exact Finset.prod_eq_one (fun i hi => hf i (Finset.mem_cons_of_mem hi))

/-- The logarithmic derivative of the inverse: `loder(f⁻¹) = -loder(f)`.
This is Corollary 7.8.16 (cor.fps.loder.inv).

Note: This does NOT require `R` to be a ℚ-algebra. -/
lemma loder_inv {f : R⟦X⟧} (hf : constantCoeff f = 1) : loder f⁻¹ = -loder f := by
  have hf_ne : constantCoeff f ≠ 0 := by simp [hf]
  have hfinv : constantCoeff f⁻¹ = 1 := by simp [constantCoeff_inv, hf]
  have h1 : loder (f * f⁻¹) = loder f + loder f⁻¹ := loder_mul hf hfinv
  have h2 : f * f⁻¹ = 1 := PowerSeries.mul_inv_cancel f hf_ne
  have h3 : loder (1 : R⟦X⟧) = 0 := by simp [loder_def]
  rw [h2, h3] at h1
  exact eq_neg_of_add_eq_zero_right h1.symm

/-- The logarithmic derivative of 1 is 0. -/
@[simp]
lemma loder_one : loder (1 : R⟦X⟧) = 0 := by
  simp [loder_def]

end LogarithmicDerivative


section ExpLogInfinite

variable {K : Type*} [CommRing K] [Algebra ℚ K]
variable {I : Type*}

omit [Algebra ℚ K] in
/-- For a summable family in `K⟦X⟧₀`, the sum is also in `K⟦X⟧₀`. -/
lemma SummableFPS₀.sum_mem (f : I → PowerSeries₀ (R := K)) (_hf : SummableFPS₀ f) :
    (∑ᶠ i, (f i).val) ∈ PowerSeries₀ := by
  rw [mem_PowerSeries₀_iff]
  -- The constant coefficient of the sum is the sum of constant coefficients
  -- Since each f i has constant term 0, the sum is 0
  have h : ∀ i, constantCoeff (f i).val = 0 := fun i => (f i).property
  rw [← coeff_zero_eq_constantCoeff_apply]
  -- Case split on whether the support of the family is finite
  by_cases hsupp : (Function.support (fun i => (f i).val)).Finite
  · -- If support is finite, use AddMonoidHom.map_finsum
    have hmap := AddMonoidHom.map_finsum ((coeff (R := K) 0).toAddMonoidHom) hsupp
    simp only [LinearMap.toAddMonoidHom_coe] at hmap
    rw [hmap]
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    rw [coeff_zero_eq_constantCoeff_apply]
    exact h i
  · -- If support is infinite, finsum is 0 by definition
    rw [finsum_of_infinite_support hsupp]
    simp


omit [Algebra ℚ K] in
/-- Helper: coefficient of product with const term 1 factors.
If `f` has constant term 1 and `f.coeff p = 0` for `1 ≤ p < k`, then
`(f * g).coeff k = f.coeff k + g.coeff k` when `g` also has constant term 1. -/
lemma coeff_mul_const_one {f g : K⟦X⟧} (hf0 : f.coeff 0 = 1) (hg0 : g.coeff 0 = 1)
    {k : ℕ} (hk : 1 ≤ k) (hf : ∀ p, 1 ≤ p → p < k → f.coeff p = 0) :
    (f * g).coeff k = f.coeff k + g.coeff k := by
  simp only [coeff_mul]
  have h0k : (0, k) ∈ HasAntidiagonal.antidiagonal k := by simp
  have hk0 : (k, 0) ∈ HasAntidiagonal.antidiagonal k := by simp
  have hne : (0, k) ≠ (k, 0) := by simp; omega
  rw [← Finset.insert_erase h0k, Finset.sum_insert (by simp [Finset.mem_erase])]
  have hk0' : (k, 0) ∈ (HasAntidiagonal.antidiagonal k).erase (0, k) := by
    simp [Finset.mem_erase, hne.symm]
  rw [← Finset.insert_erase hk0', Finset.sum_insert (by simp [Finset.mem_erase])]
  simp only [hf0, hg0, one_mul, mul_one]
  have h_rest : ∑ p ∈ ((HasAntidiagonal.antidiagonal k).erase (0, k)).erase (k, 0),
      f.coeff p.1 * g.coeff p.2 = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    simp only [Finset.mem_erase, HasAntidiagonal.mem_antidiagonal, ne_eq] at hp
    have hp_ne_k0 : p ≠ (k, 0) := hp.1
    have hp_ne_0k : p ≠ (0, k) := hp.2.1
    have hp_sum : p.1 + p.2 = k := hp.2.2
    have hp1_ne_0 : p.1 ≠ 0 := by intro h; apply hp_ne_0k; ext <;> simp_all
    have hp1_ne_k : p.1 ≠ k := by intro h; apply hp_ne_k0; ext <;> simp_all
    have hp1_pos : 1 ≤ p.1 := Nat.one_le_iff_ne_zero.mpr hp1_ne_0
    have hp1_lt : p.1 < k := by omega
    rw [hf p.1 hp1_pos hp1_lt, zero_mul]
  rw [h_rest, add_zero, add_comm]

omit [Algebra ℚ K] in
/-- If `M` is an x^n-approximator for a multipliable family with constant term 1,
then for `i ∉ M`, `(f i).coeff k = 0` for `1 ≤ k ≤ n`. -/
lemma coeff_eq_zero_of_not_mem_approximator [DecidableEq I] {f : I → K⟦X⟧}
    (hf_const : ∀ i, constantCoeff (f i) = 1)
    {n : ℕ} {M : Finset I}
    (hM : ∀ m ≤ n, ∀ J : Finset I, M ⊆ J → (∏ j ∈ J, f j).coeff m = (∏ j ∈ M, f j).coeff m)
    {i : I} (hi : i ∉ M) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (f i).coeff k = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hdet := hM k hkn (insert i M) (Finset.subset_insert i M)
    rw [Finset.prod_insert hi] at hdet
    let g := ∏ j ∈ M, f j
    have hg_const : constantCoeff g = 1 := by
      rw [map_prod]; exact Finset.prod_eq_one (fun j _ => hf_const j)
    have hfi_zero : ∀ p, 1 ≤ p → p < k → (f i).coeff p = 0 := fun p hp1 hpk =>
      ih p hpk hp1 (Nat.le_of_lt_succ (Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le hpk hkn)))
    have hfi0 : (f i).coeff 0 = 1 := by rw [coeff_zero_eq_constantCoeff_apply, hf_const]
    have hg0 : g.coeff 0 = 1 := by rw [coeff_zero_eq_constantCoeff_apply, hg_const]
    have hprod := coeff_mul_const_one hfi0 hg0 hk1 hfi_zero
    rw [hprod] at hdet
    have : (f i).coeff k + g.coeff k = g.coeff k := hdet
    have h := sub_eq_zero.mpr this
    simp at h
    exact h

omit [Algebra ℚ K] in
/-- If `X^{n+1} | g`, then `X^{n+1} | g^d` for `d ≥ 1`. -/
lemma X_pow_dvd_pow {g : K⟦X⟧} {m d : ℕ} (h : X ^ m ∣ g) (hd : d ≠ 0) :
    X ^ m ∣ g ^ d := calc X ^ m ∣ g := h
  _ ∣ g ^ d := dvd_pow_self g hd

omit [Algebra ℚ K] in
/-- If `X^{n+1} | g`, then `g.coeff n = 0`. -/
lemma coeff_zero_of_X_pow_dvd {g : K⟦X⟧} {m n : ℕ} (h : X ^ m ∣ g) (hn : n < m) :
    g.coeff n = 0 := by rw [X_pow_dvd_iff] at h; exact h n hn

omit [Algebra ℚ K] in
/-- If `f` has constant term 0 and `g.coeff k = 0` for `k ≤ n`, then `(f.subst g).coeff n = 0`. -/
lemma subst_coeff_zero_of_high_order {f g : K⟦X⟧} {n : ℕ}
    (hf : f.coeff 0 = 0) (hg : ∀ k ≤ n, g.coeff k = 0) :
    (f.subst g).coeff (Finsupp.single () n) = 0 := by
  have hg' : ∀ k < n + 1, g.coeff k = 0 := fun k hk => hg k (Nat.lt_succ_iff.mp hk)
  have hdvd : X ^ (n + 1) ∣ g := by rw [X_pow_dvd_iff]; exact hg'
  have hsub : HasSubst g := by
    apply HasSubst.of_constantCoeff_zero'
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact hg 0 (Nat.zero_le n)
  rw [coeff_subst hsub]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  rcases Nat.eq_zero_or_pos d with rfl | hd_pos
  · simp [hf]
  · have hdvd_pow : X ^ (n + 1) ∣ g ^ d := X_pow_dvd_pow hdvd (Nat.pos_iff_ne_zero.mp hd_pos)
    have h : MvPowerSeries.coeff (Finsupp.single () n) (g ^ d) = (g ^ d).coeff n := by
      simp only [PowerSeries.coeff, MvPowerSeries.coeff]
    rw [h, coeff_zero_of_X_pow_dvd hdvd_pow (Nat.lt_succ_self n), smul_zero]

/-- If `(f_i)_{i ∈ I}` is a multipliable family in `K⟦X⟧₁`, then `(Log f_i)_{i ∈ I}` is
a summable family in `K⟦X⟧₀`.

This is part of Proposition prop.fps.Exp-Log-infprod from the source material. -/
lemma Log_summable_of_multipliable (f : I → PowerSeries₁ (R := K))
    (hf : MultipliableFPS₁ f) :
    SummableFPS₀ (fun i => Log (f i)) := by
  classical
  intro n
  -- Get an x^n-approximator M for the family (f i).val
  obtain ⟨M, hM⟩ := exists_xn_approximator (fun i => (f i).val) hf n
  -- Claim: {i | (Log (f i)).val.coeff n ≠ 0} ⊆ M
  apply Set.Finite.subset M.finite_toSet
  intro i hi
  simp only [Set.mem_ofPred_eq, ne_eq] at hi
  by_contra h_not_in_M
  apply hi
  -- Log(f i) = logbar ∘ (f i - 1)
  rw [Log_val]
  -- Key: if (f i).val.coeff k = 0 for 1 ≤ k ≤ n, then (logbar.subst (f i - 1)).coeff n = 0
  have hfi_const : ∀ j, constantCoeff ((f j).val) = 1 := fun j => (f j).property
  have hfi_coeff : ∀ k, 1 ≤ k → k ≤ n → ((f i).val).coeff k = 0 := by
    intro k hk1 hkn
    exact coeff_eq_zero_of_not_mem_approximator hfi_const hM h_not_in_M hk1 hkn
  -- Now (f i).val - 1 has coeff k = 0 for 0 ≤ k ≤ n
  have hfi_sub_one_coeff : ∀ k ≤ n, ((f i).val - 1).coeff k = 0 := by
    intro k hk
    rcases k with _ | k
    · simp [hfi_const]
    · simp [hfi_coeff (k + 1) (by omega) hk]
  -- Use the substitution lemma
  have hlogbar0 : (logbar K).coeff 0 = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_logbar]
  -- The coefficient we want is (logbar.subst (f i - 1)).coeff (Finsupp.single () n)
  -- which equals (Log (f i)).val.coeff n by definition
  -- Note: (Log f).val = (logbar K).subst (f.val - 1) : MvPowerSeries Unit K
  -- and coeff n for PowerSeries = MvPowerSeries.coeff (Finsupp.single () n)
  show MvPowerSeries.coeff (Finsupp.single () n) ((logbar K).subst ((f i).val - 1)) = 0
  exact subst_coeff_zero_of_high_order hlogbar0 hfi_sub_one_coeff

/-- Log of a finite product equals the sum of logs. This is the finite version of Log_tprod,
proved by induction using Log_mul. -/
lemma Log_finprod [DecidableEq I] (s : Finset I) (f : I → PowerSeries₁ (R := K)) :
    Log (⟨∏ i ∈ s, (f i).val, by
      rw [mem_PowerSeries₁_iff, map_prod]
      exact Finset.prod_eq_one (fun i _ => (f i).property)⟩) =
    ⟨∑ i ∈ s, (Log (f i)).val, by
      rw [mem_PowerSeries₀_iff, map_sum]
      exact Finset.sum_eq_zero (fun i _ => (Log (f i)).property)⟩ := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    apply Subtype.ext
    simp only [Log_val]
    -- Need: (logbar K).subst (1 - 1) = 0
    have h0 : (1 : K⟦X⟧) - 1 = 0 := sub_self 1
    rw [h0]
    -- logbar.subst 0 = 0 since logbar has constant term 0
    have hcc : constantCoeff (logbar K) = 0 := constantCoeff_logbar
    ext n
    rw [coeff_subst' HasSubst.zero']
    simp only [map_zero]
    rw [finsum_eq_single (fun d => (coeff d (logbar K)) • (coeff n) ((0 : K⟦X⟧) ^ d)) 0]
    · simp only [pow_zero, coeff_one, smul_eq_mul]
      by_cases hn : n = 0
      · simp [hn]
      · simp [hn]
    · intro d hd
      simp only [smul_eq_mul]
      rw [zero_pow hd, map_zero, mul_zero]
  | cons a s ha ih =>
    apply Subtype.ext
    simp only [Finset.prod_cons ha, Finset.sum_cons ha]
    have hprod_mem : ∏ i ∈ s, (f i).val ∈ PowerSeries₁ := by
      rw [mem_PowerSeries₁_iff, map_prod]
      exact Finset.prod_eq_one (fun i _ => (f i).property)
    let prod_s : PowerSeries₁ (R := K) := ⟨∏ i ∈ s, (f i).val, hprod_mem⟩
    have hLog_mul := Log_mul (f a) prod_s
    have hmul_mem : (f a).val * ∏ i ∈ s, (f i).val ∈ PowerSeries₁ := by
      rw [mem_PowerSeries₁_iff, map_mul, (f a).property, map_prod]
      simp [Finset.prod_eq_one (fun i _ => (f i).property)]
    have h1 : (Log ⟨(f a).val * ∏ i ∈ s, (f i).val, hmul_mem⟩).val =
              (Log (f a)).val + (Log prod_s).val := by
      have : (f a).val * ∏ i ∈ s, (f i).val = (f a).val * prod_s.val := rfl
      simp only [this]
      exact congrArg Subtype.val hLog_mul
    rw [h1]
    have h2 : (Log prod_s).val = ∑ i ∈ s, (Log (f i)).val := congrArg Subtype.val ih
    rw [h2]

/-- Helper lemma: if two FPS have the same first n+1 coefficients and both have constant term 0,
then their images under `logbar.subst` have the same n-th coefficient.

This follows from the fact that `(logbar.subst g).coeff n` only depends on `g.coeff 0, ..., g.coeff n`. -/
lemma logbar_subst_coeff_eq_of_coeff_eq {g₁ g₂ : K⟦X⟧} {n : ℕ}
    (hg₁ : constantCoeff g₁ = 0) (hg₂ : constantCoeff g₂ = 0)
    (heq : ∀ m ≤ n, g₁.coeff m = g₂.coeff m) :
    coeff n ((logbar K).subst g₁) = coeff n ((logbar K).subst g₂) := by
  have hsub₁ : HasSubst g₁ := HasSubst.of_constantCoeff_zero' hg₁
  have hsub₂ : HasSubst g₂ := HasSubst.of_constantCoeff_zero' hg₂
  rw [coeff_subst' hsub₁, coeff_subst' hsub₂]
  apply finsum_congr
  intro d
  by_cases hd : d = 0
  · simp [hd]
  · congr 1
    -- Show g₁^d and g₂^d have the same n-th coefficient
    -- We prove this by showing that coeff m (g₁^d) = coeff m (g₂^d) for all m ≤ n
    -- by induction on d
    have hpow : ∀ d' : ℕ, ∀ m ≤ n, coeff m (g₁ ^ d') = coeff m (g₂ ^ d') := by
      intro d'
      induction d' with
      | zero => simp
      | succ d' ih =>
        intro m hm
        rw [pow_succ g₁, pow_succ g₂]
        simp only [coeff_mul]
        apply Finset.sum_congr rfl
        intro ⟨p, q⟩ hpq
        simp only [HasAntidiagonal.mem_antidiagonal] at hpq
        have hp : p ≤ n := by omega
        have hq : q ≤ n := by omega
        rw [ih p hp, heq q hq]
    exact hpow d n (le_refl n)

/-- **Proposition prop.fps.Exp-Log-infprod**: Log converts infinite products to infinite sums.

If `(f_i)_{i ∈ I}` is a multipliable family of FPSs in `K⟦X⟧₁`, then:
1. `(Log f_i)_{i ∈ I}` is a summable family of FPSs in `K⟦X⟧₀`
2. `∏_{i ∈ I} f_i ∈ K⟦X⟧₁`
3. `Log(∏_{i ∈ I} f_i) = ∑_{i ∈ I} Log(f_i)`

This is the infinite version of `Log_mul`: `Log(fg) = Log(f) + Log(g)`.

The proof strategy:
1. Use `Log_mul` for finite products
2. Show that for multipliable families, the finite partial products converge
3. Use continuity of Log (which follows from the coefficient-wise definition)
   to pass to the limit
-/
lemma Log_tprod (f : I → PowerSeries₁ (R := K))
    (hf : MultipliableFPS₁ f)
    (hf_sum : SummableFPS₀ (fun i => Log (f i)) := Log_summable_of_multipliable f hf) :
    Log (multipliableFPS₁Prod f hf) = summableFPS₀Sum (fun i => Log (f i)) hf_sum := by
  classical
  -- The proof proceeds by showing equality of all coefficients
  apply Subtype.ext
  ext n

  -- Get an x^n-approximator for the product
  obtain ⟨M, hM⟩ := exists_xn_approximator (fun i => (f i).val) hf n

  -- For the finite product, use Log_finprod
  have hfinprod := Log_finprod M f

  -- Step 1: Show that Log(tprod f) has the same n-th coefficient as Log(∏_{i∈M} f_i)
  -- This uses the helper lemma logbar_subst_coeff_eq_of_coeff_eq

  -- The tprod has the same first n+1 coefficients as the finite product over M
  have htprod_eq : ∀ m ≤ n, (tprod (fun i => (f i).val) hf).coeff m = (∏ i ∈ M, (f i).val).coeff m := by
    intro m hm
    exact tprod_coeff hf (hM m hm)

  -- Both tprod - 1 and (∏_{i∈M} f_i) - 1 have constant term 0
  have htprod_const : constantCoeff (tprod (fun i => (f i).val) hf) = 1 :=
    (multipliableFPS₁Prod f hf).property
  have hfinprod_const : constantCoeff (∏ i ∈ M, (f i).val) = 1 := by
    rw [map_prod]; exact Finset.prod_eq_one (fun i _ => (f i).property)

  have htprod_sub_const : constantCoeff (tprod (fun i => (f i).val) hf - 1) = 0 := by
    simp [htprod_const]
  have hfinprod_sub_const : constantCoeff (∏ i ∈ M, (f i).val - 1) = 0 := by
    simp [hfinprod_const]

  -- The differences have the same first n+1 coefficients
  have hdiff_eq : ∀ m ≤ n, (tprod (fun i => (f i).val) hf - 1).coeff m =
      (∏ i ∈ M, (f i).val - 1).coeff m := by
    intro m hm
    simp only [map_sub]
    rw [htprod_eq m hm]

  -- Apply the helper lemma to get equality of Log coefficients
  have hLog_coeff_eq : coeff n ((logbar K).subst (tprod (fun i => (f i).val) hf - 1)) =
      coeff n ((logbar K).subst (∏ i ∈ M, (f i).val - 1)) :=
    logbar_subst_coeff_eq_of_coeff_eq htprod_sub_const hfinprod_sub_const hdiff_eq

  -- Rewrite using Log definition
  have hLog_tprod : (Log (multipliableFPS₁Prod f hf)).val = (logbar K).subst (tprod (fun i => (f i).val) hf - 1) := by
    simp only [Log_val, multipliableFPS₁Prod]
  have hLog_finprod_val : ((logbar K).subst (∏ i ∈ M, (f i).val - 1)) =
      (Log ⟨∏ i ∈ M, (f i).val, by rw [mem_PowerSeries₁_iff]; exact hfinprod_const⟩).val := by
    simp only [Log_val]

  -- Step 2: Show that the n-th coefficient of the coefficient-wise sum equals that of ∑_{i∈M} Log(f_i)
  -- This uses summability: for i ∉ M, (Log(f_i)).coeff n = 0
  --
  -- With the coefficient-wise definition of summableFPS₀Sum, we need to show:
  --   ∑ᶠ i, coeff n (Log (f i)).val = (∑ i ∈ M, (Log (f i)).val).coeff n
  -- This is simpler than the old approach since we don't need to case split on infinite support.

  have hsum_coeff_eq : (∑ᶠ i, coeff n (Log (f i)).val) = (∑ i ∈ M, (Log (f i)).val).coeff n := by
    -- The key is that for i ∉ M, (Log(f_i)).val.coeff n = 0
    have hzero_outside : ∀ i ∉ M, (Log (f i)).val.coeff n = 0 := by
      intro i hi
      rw [Log_val]
      have hfi_const : ∀ j, constantCoeff ((f j).val) = 1 := fun j => (f j).property
      have hfi_coeff : ∀ k, 1 ≤ k → k ≤ n → ((f i).val).coeff k = 0 := by
        intro k hk1 hkn
        exact coeff_eq_zero_of_not_mem_approximator hfi_const hM hi hk1 hkn
      have hfi_sub_one_coeff : ∀ k ≤ n, ((f i).val - 1).coeff k = 0 := by
        intro k hk
        rcases k with _ | k
        · simp [hfi_const]
        · simp [hfi_coeff (k + 1) (by omega) hk]
      have hlogbar0 : (logbar K).coeff 0 = 0 := by
        rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_logbar]
      exact subst_coeff_zero_of_high_order hlogbar0 hfi_sub_one_coeff

    -- The support of (fun i => (Log (f i)).val.coeff n) is contained in M
    have hsupp : Function.support (fun i => (Log (f i)).val.coeff n) ⊆ M := by
      intro i hi
      simp only [Function.mem_support, ne_eq] at hi
      by_contra h
      exact hi (hzero_outside i h)

    -- Use finsum_eq_sum_of_support_subset since support is contained in finite set M
    rw [finsum_eq_sum_of_support_subset _ hsupp]
    -- And coeff n ∘ sum = sum ∘ coeff n
    rw [map_sum]

  -- Combine everything
  simp only [summableFPS₀Sum, multipliableFPS₁Prod] at *
  rw [hLog_tprod, hLog_coeff_eq, hLog_finprod_val]
  -- The RHS is (coeff n) (mk fun n => ∑ᶠ i, (coeff n) (Log (f i)).val)
  -- Use coeff_mk to simplify this to ∑ᶠ i, (coeff n) (Log (f i)).val
  rw [coeff_mk]
  rw [hsum_coeff_eq]
  -- Now use Log_finprod to connect Log(∏_{i∈M} f_i) = ∑_{i∈M} Log(f_i)
  have hfinprod_eq := congrArg Subtype.val hfinprod
  simp only at hfinprod_eq
  rw [← hfinprod_eq]


/-- The dual statement: Exp converts infinite sums to infinite products.

This is Proposition prop.fps.Exp-Log-infsum from the source material.

If `(g_i)_{i ∈ I}` is a summable family of FPSs in `K⟦X⟧₀`, then:
1. `(Exp g_i)_{i ∈ I}` is a multipliable family of FPSs in `K⟦X⟧₁`
2. `∑_{i ∈ I} g_i ∈ K⟦X⟧₀`
3. `Exp(∑_{i ∈ I} g_i) = ∏_{i ∈ I} Exp(g_i)`

This is the infinite version of `Exp_add`: `Exp(f + g) = Exp(f) · Exp(g)`. -/
-- Helper lemma: if g has order > n, then (expbar).subst g has order > n
lemma expbar_subst_order (g : K⟦X⟧) (hg : constantCoeff g = 0) (n : ℕ) (hord : n < order g) :
    n < order ((expbar K).subst g) := by
  calc (n : ℕ∞) < order g := hord
    _ ≤ order ((expbar K).subst g) := le_order_subst_right' hg constantCoeff_expbar

-- Helper lemma: if g.coeff k = 0 for all k ≤ n, then ((expbar K).subst g).coeff n = 0
lemma expbar_subst_coeff_zero (g : K⟦X⟧) (hg : constantCoeff g = 0) (n : ℕ)
    (hcoeff : ∀ k ≤ n, coeff k g = 0) :
    coeff n ((expbar K).subst g) = 0 := by
  have hord : n < order g := by
    by_contra h
    push Not at h
    have hord_le : order g ≤ n := h
    cases hord' : order g with
    | top => rw [hord'] at hord_le; simp at hord_le
    | coe m =>
      have hne : coeff m g ≠ 0 := by rw [order_eq_nat] at hord'; exact hord'.1
      have hm_le : m ≤ n := by rw [hord'] at hord_le; exact ENat.coe_le_coe.mp hord_le
      exact hne (hcoeff m hm_le)
  have hord' := expbar_subst_order g hg n hord
  exact coeff_of_lt_order n hord'

lemma Exp_multipliable_of_summable (g : I → PowerSeries₀ (R := K))
    (hg : SummableFPS₀ g) :
    MultipliableFPS₁ (fun i => Exp (g i)) := by
  -- The key insight is that Exp(g) = exp ∘ g = 1 + expbar ∘ g.
  -- For a summable family in K⟦X⟧₀, the family (expbar ∘ g_i) is also summable
  -- (in the coefficient sense), making (1 + expbar ∘ g_i) = (Exp g_i) multipliable.

  -- First, show that (Exp (g i)).val = 1 + (expbar K).subst (g i).val
  have hExp_eq : ∀ i, (Exp (g i)).val = 1 + (expbar K).subst (g i).val := fun i => by
    simp only [Exp_val]
    have hgi : constantCoeff (g i).val = 0 := (g i).property
    have hsub : HasSubst (g i).val := HasSubst.of_constantCoeff_zero' hgi
    calc (exp K).subst (g i).val
        = (1 + expbar K).subst (g i).val := by rw [expbar]; ring_nf
        _ = 1 + (expbar K).subst (g i).val := by
            rw [subst_add hsub, ← coe_substAlgHom hsub, map_one]

  -- Rewrite the goal using this equality
  unfold MultipliableFPS₁
  have heq : (fun i => (Exp (g i)).val) = (fun i => 1 + (expbar K).subst (g i).val) := by
    funext i; exact hExp_eq i
  rw [heq]

  -- Apply multipliable_one_add_of_summable from InfiniteProducts.lean
  apply multipliable_one_add_of_summable
  intro n

  -- Show that {i | coeff n ((expbar K).subst (g i).val) ≠ 0} is finite
  -- Key: if (g i).val.coeff k = 0 for all k ≤ n, then ((expbar K).subst (g i).val).coeff n = 0
  have hsub : {i : I | coeff n ((expbar K).subst (g i).val) ≠ 0} ⊆
              ⋃ k ∈ Finset.range (n + 1), {i : I | coeff k (g i).val ≠ 0} := by
    intro i hi
    simp only [Set.mem_ofPred_eq] at hi
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq]
    by_contra h
    push Not at h
    have hcoeff : ∀ k ≤ n, coeff k (g i).val = 0 := by
      intro k hk
      have hk' : k < n + 1 := Nat.lt_succ_of_le hk
      by_contra hne
      exact hne (h k hk')
    have := expbar_subst_coeff_zero (g i).val (g i).property n hcoeff
    exact hi this

  apply Set.Finite.subset _ hsub
  apply Set.Finite.biUnion
  · exact (Finset.range (n + 1)).finite_toSet
  · intro k _
    exact hg k

/-- Exp converts infinite sums to infinite products.

This is the infinite version of `Exp_add`. -/
lemma Exp_sum (g : I → PowerSeries₀ (R := K))
    (hg : SummableFPS₀ g)
    (hg_mul : MultipliableFPS₁ (fun i => Exp (g i)) := Exp_multipliable_of_summable g hg) :
    Exp (summableFPS₀Sum g hg) = multipliableFPS₁Prod (fun i => Exp (g i)) hg_mul := by
  -- This is derived from Log_tprod using the fact that Exp and Log are inverses.
  -- Let f_i = Exp(g_i). Then:
  -- 1. Log(∏ f_i) = ∑ Log(f_i) by Log_tprod
  -- 2. Log(Exp(g_i)) = g_i by Log_Exp
  -- 3. So ∑ Log(f_i) = ∑ g_i
  -- 4. Applying Exp: Exp(Log(∏ f_i)) = Exp(∑ g_i)
  -- 5. By Exp_Log: ∏ f_i = Exp(∑ g_i)

  -- Define f_i = Exp(g_i)
  let f : I → PowerSeries₁ (R := K) := fun i => Exp (g i)

  -- Show that Log(Exp(g_i)) = g_i for all i
  have hLogExp : ∀ i, Log (f i) = g i := fun i => Log_Exp (g i)

  -- The summability of (Log(f_i)) follows from hLogExp and hg
  have hf_sum : SummableFPS₀ (fun i => Log (f i)) := by
    intro n
    convert hg n using 1
    ext i
    simp only [Set.mem_ofPred_eq]
    rw [hLogExp i]

  -- Apply Log_tprod: Log(∏ f_i) = ∑ Log(f_i)
  have hLog_prod := Log_tprod f hg_mul hf_sum

  -- Apply Exp to both sides and use Exp_Log
  have h1 : Exp (Log (multipliableFPS₁Prod f hg_mul)) = multipliableFPS₁Prod f hg_mul :=
    Exp_Log (multipliableFPS₁Prod f hg_mul)

  rw [← h1, hLog_prod]

  -- Now need: Exp(summableFPS₀Sum (Log ∘ f) hf_sum) = Exp(summableFPS₀Sum g hg)
  -- This follows from showing the sums are equal
  congr 1

  -- Show summableFPS₀Sum (fun i => Log (f i)) hf_sum = summableFPS₀Sum g hg
  apply Subtype.ext
  simp only [summableFPS₀Sum]
  -- Need: mk (fun n => ∑ᶠ i, (Log (f i)).val.coeff n) = mk (fun n => ∑ᶠ i, (g i).val.coeff n)
  congr 1
  funext n
  congr 1
  funext i
  exact congrArg (fun x => x.val.coeff n) (hLogExp i).symm

end ExpLogInfinite

end PowerSeries
end


/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_coeff_logbar
  [CommRing K]
  [Algebra ℚ K]
-- given
  (n : ℕ) :
-- imply
  coeff n (logbar K) = if n = 0 then 0 else algebraMap ℚ K ((-1 : ℚ) ^ (n - 1) / n) := by
-- proof
  apply PowerSeries.coeff_logbar n

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_constantCoeff_logbar
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  constantCoeff (logbar K) = 0 := by
-- proof
  apply PowerSeries.constantCoeff_logbar

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_coeff_expbar
  [CommRing K]
  [Algebra ℚ K]
-- given
  (n : ℕ) :
-- imply
  coeff n (expbar K) = if n = 0 then 0 else algebraMap ℚ K (1 / Nat.factorial n) := by
-- proof
  apply PowerSeries.coeff_expbar n

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_constantCoeff_expbar
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  constantCoeff (expbar K) = 0 := by
-- proof
  apply PowerSeries.constantCoeff_expbar

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_expbar_eq_exp_sub_one
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  expbar K = exp K - 1 := by
-- proof
  apply PowerSeries.expbar_eq_exp_sub_one

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_coeff_exp_zero
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  coeff 0 (exp K) = 1 := by
-- proof
  apply PowerSeries.coeff_exp_zero

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_coeff_exp_one
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  coeff 1 (exp K) = 1 := by
-- proof
  apply PowerSeries.coeff_exp_one

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_coeff_logbar_zero
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  coeff 0 (logbar K) = 0 := by
-- proof
  apply PowerSeries.coeff_logbar_zero

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_coeff_logbar_one
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  coeff 1 (logbar K) = 1 := by
-- proof
  apply PowerSeries.coeff_logbar_one

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_coeff_expbar_zero
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  coeff 0 (expbar K) = 0 := by
-- proof
  apply PowerSeries.coeff_expbar_zero

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_coeff_expbar_one
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  coeff 1 (expbar K) = 1 := by
-- proof
  apply PowerSeries.coeff_expbar_one

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_logbar_eq_sum_alternating
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  logbar K = mk fun n => if n = 0 then 0 else algebraMap ℚ K ((-1 : ℚ) ^ (n - 1) / n) := by
-- proof
  apply PowerSeries.logbar_eq_sum_alternating

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_exp_constantCoeff
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  constantCoeff (exp K) = 1 := by
-- proof
  apply PowerSeries.exp_constantCoeff

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_logbar_constantCoeff
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  constantCoeff (logbar K) = 0 := by
-- proof
  apply PowerSeries.logbar_constantCoeff

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_expbar_constantCoeff
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  constantCoeff (expbar K) = 0 := by
-- proof
  apply PowerSeries.expbar_constantCoeff

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_exp_eq_one_add_expbar
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  exp K = 1 + expbar K := by
-- proof
  apply PowerSeries.exp_eq_one_add_expbar

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_coeff_invOnePlusX
  [CommRing K]
  [Algebra ℚ K]
-- given
  (n : ℕ) :
-- imply
  coeff n (invOnePlusX K) = algebraMap ℚ K ((-1 : ℚ) ^ n) := by
-- proof
  apply PowerSeries.coeff_invOnePlusX K n

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_derivative_logbar
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  PowerSeries.derivative (logbar K) = invOnePlusX K := by
-- proof
  apply PowerSeries.derivative_logbar

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_derivative_expbar
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  PowerSeries.derivative (expbar K) = exp K := by
-- proof
  apply PowerSeries.derivative_expbar

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_derivative_exp_comp
  [CommRing K]
  [Algebra ℚ K]
  {g : K⟦X⟧}
-- given
  (hg : constantCoeff g = 0) :
-- imply
  PowerSeries.derivative ((exp K).subst g) = (exp K).subst g * PowerSeries.derivative g := by
-- proof
  apply PowerSeries.derivative_exp_comp hg

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_derivative_expbar_comp
  [CommRing K]
  [Algebra ℚ K]
  {g : K⟦X⟧}
-- given
  (hg : constantCoeff g = 0) :
-- imply
  PowerSeries.derivative ((expbar K).subst g) = (exp K).subst g * PowerSeries.derivative g := by
-- proof
  apply PowerSeries.derivative_expbar_comp hg

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_invOnePlusX_mul_one_add_X
  [Field K]
  [Algebra ℚ K] :
-- imply
  invOnePlusX K * (1 + X) = 1 := by
-- proof
  apply PowerSeries.invOnePlusX_mul_one_add_X

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_invOnePlusX_subst_eq_inv
  [Field K]
  [Algebra ℚ K]
  {g : K⟦X⟧}
-- given
  (hg : constantCoeff g = 0) :
-- imply
  (invOnePlusX K).subst g = (1 + g)⁻¹ := by
-- proof
  apply PowerSeries.invOnePlusX_subst_eq_inv hg

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_derivative_logbar_comp
  [Field K]
  [Algebra ℚ K]
  {g : K⟦X⟧}
-- given
  (hg : constantCoeff g = 0) :
-- imply
  PowerSeries.derivative ((logbar K).subst g) = (1 + g)⁻¹ * PowerSeries.derivative g := by
-- proof
  apply PowerSeries.derivative_logbar_comp hg

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_logbar_comp_expbar'
  [Field K]
  [Algebra ℚ K] :
-- imply
  (logbar K).subst (expbar K) = X := by
-- proof
  apply PowerSeries.logbar_comp_expbar'

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_constantCoeff_subst_eq_apply
  [CommRing K]
  {f g : K⟦X⟧}
-- given
  (hg : constantCoeff g = 0) :
-- imply
  constantCoeff (f.subst g) = constantCoeff f := by
-- proof
  apply PowerSeries.constantCoeff_subst_eq_apply hg

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_eq_of_derivative_eq_mul_of_inv
  [CommRing K]
  [Algebra ℚ K]
  {h₁ h₂ g : K⟦X⟧}
-- given
  (hd₁ : PowerSeries.derivative h₁ = (1 + h₁) * g)
  (hd₂ : PowerSeries.derivative h₂ = (1 + h₂) * g)
  (hc : constantCoeff h₁ = constantCoeff h₂) :
-- imply
  h₁ = h₂ := by
-- proof
  apply PowerSeries.eq_of_derivative_eq_mul_of_inv hd₁ hd₂ hc

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_expbar_comp_logbar
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  (expbar K).subst (logbar K) = X := by
-- proof
  apply PowerSeries.expbar_comp_logbar

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_invOnePlusX_subst_expbar_mul_exp
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  (invOnePlusX K).subst (expbar K) * exp K = 1 := by
-- proof
  apply PowerSeries.invOnePlusX_subst_expbar_mul_exp

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_eq_of_derivative_eq_one
  [CommRing K]
  [Algebra ℚ K]
  {h₁ h₂ : K⟦X⟧}
-- given
  (hd₁ : PowerSeries.derivative h₁ = 1)
  (hd₂ : PowerSeries.derivative h₂ = 1)
  (hc : constantCoeff h₁ = constantCoeff h₂) :
-- imply
  h₁ = h₂ := by
-- proof
  apply PowerSeries.eq_of_derivative_eq_one hd₁ hd₂ hc

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_logbar_comp_expbar
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  (logbar K).subst (expbar K) = X := by
-- proof
  apply PowerSeries.logbar_comp_expbar

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_mem_PowerSeries₀_iff
  [CommRing R]
  {f : R⟦X⟧} :
-- imply
  f ∈ PowerSeries₀ ↔ constantCoeff f = 0 := by
-- proof
  apply PowerSeries.mem_PowerSeries₀_iff

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_mem_PowerSeries₁_iff
  [CommRing R]
  {f : R⟦X⟧} :
-- imply
  f ∈ PowerSeries₁ ↔ constantCoeff f = 1 := by
-- proof
  apply PowerSeries.mem_PowerSeries₁_iff

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_X_mem_PowerSeries₀
  [CommRing R] :
-- imply
  (X : R⟦X⟧) ∈ PowerSeries₀ := by
-- proof
  apply PowerSeries.X_mem_PowerSeries₀

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_zero_mem
  [CommRing R] :
-- imply
  (0 : R⟦X⟧) ∈ PowerSeries₀ := by
-- proof
  apply PowerSeries.PowerSeries₀.zero_mem

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_add_mem
  [CommRing R]
  {f g : R⟦X⟧}
-- given
  (hf : f ∈ PowerSeries₀)
  (hg : g ∈ PowerSeries₀) :
-- imply
  f + g ∈ PowerSeries₀ := by
-- proof
  apply PowerSeries.PowerSeries₀.add_mem hf hg

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_neg_mem
  [CommRing R]
  {f : R⟦X⟧}
-- given
  (hf : f ∈ PowerSeries₀) :
-- imply
  -f ∈ PowerSeries₀ := by
-- proof
  apply PowerSeries.PowerSeries₀.neg_mem hf

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_sub_mem
  [CommRing R]
  {f g : R⟦X⟧}
-- given
  (hf : f ∈ PowerSeries₀)
  (hg : g ∈ PowerSeries₀) :
-- imply
  f - g ∈ PowerSeries₀ := by
-- proof
  apply PowerSeries.PowerSeries₀.sub_mem hf hg

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_one_mem
  [CommRing R] :
-- imply
  (1 : R⟦X⟧) ∈ PowerSeries₁ := by
-- proof
  apply PowerSeries.PowerSeries₁.one_mem

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_mul_mem
  [CommRing R]
  {f g : R⟦X⟧}
-- given
  (hf : f ∈ PowerSeries₁)
  (hg : g ∈ PowerSeries₁) :
-- imply
  f * g ∈ PowerSeries₁ := by
-- proof
  apply PowerSeries.PowerSeries₁.mul_mem hf hg

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_sub_one_mem_PowerSeries₀
  [CommRing R]
  {f : R⟦X⟧}
-- given
  (hf : f ∈ PowerSeries₁) :
-- imply
  f - 1 ∈ PowerSeries₀ := by
-- proof
  apply PowerSeries.sub_one_mem_PowerSeries₀ hf

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_inv_mem
  [Field R]
  {f : R⟦X⟧}
-- given
  (hf : f ∈ PowerSeries₁) :
-- imply
  f⁻¹ ∈ PowerSeries₁ := by
-- proof
  apply PowerSeries.PowerSeries₁.inv_mem hf

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_div_mem
  [Field R]
  {f g : R⟦X⟧}
-- given
  (hf : f ∈ PowerSeries₁)
  (hg : g ∈ PowerSeries₁) :
-- imply
  f * g⁻¹ ∈ PowerSeries₁ := by
-- proof
  apply PowerSeries.PowerSeries₁.div_mem hf hg

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_exp_mem_PowerSeries₁
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  exp K ∈ PowerSeries₁ := by
-- proof
  apply PowerSeries.exp_mem_PowerSeries₁

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_logbar_mem_PowerSeries₀
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  logbar K ∈ PowerSeries₀ := by
-- proof
  apply PowerSeries.logbar_mem_PowerSeries₀

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_expbar_mem_PowerSeries₀
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  expbar K ∈ PowerSeries₀ := by
-- proof
  apply PowerSeries.expbar_mem_PowerSeries₀

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_subst_mem
  [CommRing K]
  {f g : K⟦X⟧}
-- given
  (hf : f ∈ PowerSeries₀)
  (hg : g ∈ PowerSeries₀) :
-- imply
  f.subst g ∈ PowerSeries₀ := by
-- proof
  apply PowerSeries.PowerSeries₀.subst_mem hf hg

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_PowerSeries₁_subst_mem
  [CommRing K]
  {f g : K⟦X⟧}
-- given
  (hf : f ∈ PowerSeries₁)
  (hg : g ∈ PowerSeries₀) :
-- imply
  f.subst g ∈ PowerSeries₁ := by
-- proof
  apply PowerSeries.PowerSeries₁.subst_mem hf hg

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_exp_subst_mem_PowerSeries₁
  [CommRing K]
  [Algebra ℚ K]
  {g : K⟦X⟧}
-- given
  (hg : g ∈ PowerSeries₀) :
-- imply
  (exp K).subst g ∈ PowerSeries₁ := by
-- proof
  apply PowerSeries.exp_subst_mem_PowerSeries₁ hg

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_logbar_subst_sub_one_mem_PowerSeries₀
  [CommRing K]
  [Algebra ℚ K]
  {f : K⟦X⟧}
-- given
  (hf : f ∈ PowerSeries₁) :
-- imply
  (logbar K).subst (f - 1) ∈ PowerSeries₀ := by
-- proof
  apply PowerSeries.logbar_subst_sub_one_mem_PowerSeries₀ hf

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_Exp_val
  [CommRing K]
  [Algebra ℚ K]
-- given
  (g : PowerSeries₀ (R := K)) :
-- imply
  (Exp g).val = (exp K).subst g.val := by
-- proof
  apply PowerSeries.Exp_val g

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_Log_val
  [CommRing K]
  [Algebra ℚ K]
-- given
  (f : PowerSeries₁ (R := K)) :
-- imply
  (Log f).val = (logbar K).subst (f.val - 1) := by
-- proof
  apply PowerSeries.Log_val f

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_Log_Exp
  [CommRing K]
  [Algebra ℚ K]
-- given
  (g : PowerSeries₀ (R := K)) :
-- imply
  Log (Exp g) = g := by
-- proof
  apply PowerSeries.Log_Exp g

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_Exp_Log
  [CommRing K]
  [Algebra ℚ K]
-- given
  (f : PowerSeries₁ (R := K)) :
-- imply
  Exp (Log f) = f := by
-- proof
  apply PowerSeries.Exp_Log f

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_Exp_Log_inverse
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  Function.LeftInverse (Log (K := K)) Exp ∧ Function.RightInverse (Log (K := K)) Exp := by
-- proof
  apply PowerSeries.Exp_Log_inverse

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_eq_of_derivative_eq_mul_self
  [CommRing K]
  [Algebra ℚ K]
  {h₁ h₂ g : K⟦X⟧}
-- given
  (hd₁ : PowerSeries.derivative h₁ = h₁ * g)
  (hd₂ : PowerSeries.derivative h₂ = h₂ * g)
  (hc : constantCoeff h₁ = constantCoeff h₂) :
-- imply
  h₁ = h₂ := by
-- proof
  apply PowerSeries.eq_of_derivative_eq_mul_self hd₁ hd₂ hc

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_Exp_add
  [CommRing K]
  [Algebra ℚ K]
-- given
  (f g : PowerSeries₀ (R := K)) :
-- imply
  Exp (⟨f.val + g.val, by rw [mem_PowerSeries₀_iff, map_add, f.property, g.property, add_zero]⟩) = ⟨(Exp f).val * (Exp g).val, by rw [mem_PowerSeries₁_iff, map_mul, (Exp f).property, (Exp g).property, one_mul]⟩ := by
-- proof
  apply PowerSeries.Exp_add f g

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_Log_mul
  [CommRing K]
  [Algebra ℚ K]
-- given
  (f g : PowerSeries₁ (R := K)) :
-- imply
  Log (⟨f.val * g.val, by rw [mem_PowerSeries₁_iff, map_mul, f.property, g.property, one_mul]⟩) = ⟨(Log f).val + (Log g).val, by rw [mem_PowerSeries₀_iff, map_add, (Log f).property, (Log g).property, add_zero]⟩ := by
-- proof
  apply PowerSeries.Log_mul f g

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_Exp_isAddGroupHom
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  ∀ f g : PowerSeries₀ (R := K), Exp (⟨f.val + g.val, PowerSeries₀.add_mem f.property g.property⟩) = ⟨(Exp f).val * (Exp g).val, PowerSeries₁.mul_mem (Exp f).property (Exp g).property⟩ := by
-- proof
  apply PowerSeries.Exp_isAddGroupHom

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_Exp_zero
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  Exp (⟨0, PowerSeries₀.zero_mem⟩ : PowerSeries₀ (R := K)) = ⟨1, PowerSeries₁.one_mem⟩ := by
-- proof
  apply PowerSeries.Exp_zero

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_Log_one
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  Log (⟨1, PowerSeries₁.one_mem⟩ : PowerSeries₁ (R := K)) = ⟨0, PowerSeries₀.zero_mem⟩ := by
-- proof
  apply PowerSeries.Log_one

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_Exp_Log_groupIso
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  (Function.LeftInverse (Log (K := K)) Exp ∧ Function.RightInverse (Log (K := K)) Exp) ∧ (∀ f g : PowerSeries₀ (R := K), Exp ⟨f.val + g.val, PowerSeries₀.add_mem f.property g.property⟩ = ⟨(Exp f).val * (Exp g).val, PowerSeries₁.mul_mem (Exp f).property (Exp g).property⟩) ∧ (Exp (⟨0, PowerSeries₀.zero_mem⟩ : PowerSeries₀ (R := K)) = ⟨1, PowerSeries₁.one_mem⟩) := by
-- proof
  apply PowerSeries.Exp_Log_groupIso

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_loder_def
  [Field R]
-- given
  (f : R⟦X⟧) :
-- imply
  loder f = PowerSeries.derivative f * f⁻¹ := by
-- proof
  apply PowerSeries.loder_def f

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_isUnit_of_constantCoeff_eq_one
  [Field R]
  {f : R⟦X⟧}
-- given
  (hf : constantCoeff f = 1) :
-- imply
  IsUnit f := by
-- proof
  apply PowerSeries.isUnit_of_constantCoeff_eq_one hf

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_isUnit_iff_constantCoeff_isUnit
  [Field R]
  {f : R⟦X⟧} :
-- imply
  IsUnit f ↔ IsUnit (constantCoeff f) := by
-- proof
  apply PowerSeries.isUnit_iff_constantCoeff_isUnit

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_mul_inv_cancel_of_constantCoeff_eq_one
  [Field R]
  {f : R⟦X⟧}
-- given
  (hf : constantCoeff f = 1) :
-- imply
  f * f⁻¹ = 1 := by
-- proof
  apply PowerSeries.mul_inv_cancel_of_constantCoeff_eq_one hf

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_inv_mul_cancel_of_constantCoeff_eq_one
  [Field R]
  {f : R⟦X⟧}
-- given
  (hf : constantCoeff f = 1) :
-- imply
  f⁻¹ * f = 1 := by
-- proof
  apply PowerSeries.inv_mul_cancel_of_constantCoeff_eq_one hf

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_constantCoeff_inv_of_constantCoeff_eq_one
  [Field R]
  {f : R⟦X⟧}
-- given
  (hf : constantCoeff f = 1) :
-- imply
  constantCoeff f⁻¹ = 1 := by
-- proof
  apply PowerSeries.constantCoeff_inv_of_constantCoeff_eq_one hf

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_invOnePlusX_eq_inv
  [Field R]
  [Algebra ℚ R] :
-- imply
  invOnePlusX R = (1 + X)⁻¹ := by
-- proof
  apply PowerSeries.invOnePlusX_eq_inv

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_subst_inv_of_mul_eq_one
  [Field R]
  {g a b : R⟦X⟧}
-- given
  (hg : HasSubst g)
  (hab : a * b = 1) :
-- imply
  (a.subst g)⁻¹ = b.subst g := by
-- proof
  apply PowerSeries.subst_inv_of_mul_eq_one hg hab

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_loder_eq_derivative_Log
  [Field R]
  [Algebra ℚ R]
  {f : R⟦X⟧}
-- given
  (hf : constantCoeff f = 1) :
-- imply
  loder f = PowerSeries.derivative ((logbar R).subst (f - 1)) := by
-- proof
  apply PowerSeries.loder_eq_derivative_Log hf

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_loder_mul
  [Field R]
  {f g : R⟦X⟧}
-- given
  (hf : constantCoeff f = 1)
  (hg : constantCoeff g = 1) :
-- imply
  loder (f * g) = loder f + loder g := by
-- proof
  apply PowerSeries.loder_mul hf hg

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_loder_prod
  [Field R]
-- given
  (s : Finset ι)
  (f : ι → R⟦X⟧)
  (hf : ∀ i ∈ s, constantCoeff (f i) = 1) :
-- imply
  loder (∏ i ∈ s, f i) = ∑ i ∈ s, loder (f i) := by
-- proof
  apply PowerSeries.loder_prod s f hf

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_loder_inv
  [Field R]
  {f : R⟦X⟧}
-- given
  (hf : constantCoeff f = 1) :
-- imply
  loder f⁻¹ = -loder f := by
-- proof
  apply PowerSeries.loder_inv hf

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_loder_one
  [Field R] :
-- imply
  loder (1 : R⟦X⟧) = 0 := by
-- proof
  apply PowerSeries.loder_one

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_sum_mem
  [CommRing K]
-- given
  (f : I → PowerSeries₀ (R := K))
  (hf : SummableFPS₀ f) :
-- imply
  (finsum (fun i => (f i).val)) ∈ PowerSeries₀ := by
-- proof
  apply PowerSeries.SummableFPS₀.sum_mem f hf

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_prod_mem
  [CommRing K]
-- given
  (f : I → PowerSeries₁ (R := K))
  (hf : MultipliableFPS₁ f) :
-- imply
  PowerSeries.tprod (fun i => (f i).val) hf ∈ PowerSeries₁ := by
-- proof
  apply PowerSeries.MultipliableFPS₁.prod_mem f hf

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_Log_summable_of_multipliable
  [CommRing K]
  [Algebra ℚ K]
-- given
  (f : I → PowerSeries₁ (R := K))
  (hf : MultipliableFPS₁ f) :
-- imply
  SummableFPS₀ (fun i => Log (f i)) := by
-- proof
  apply PowerSeries.Log_summable_of_multipliable f hf

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_Log_tprod
  [CommRing K]
  [Algebra ℚ K]
-- given
  (f : I → PowerSeries₁ (R := K))
  (hf : MultipliableFPS₁ f)
  (hf_sum : SummableFPS₀ (fun i => Log (f i)) := Log_summable_of_multipliable f hf) :
-- imply
  Log (multipliableFPS₁Prod f hf) = summableFPS₀Sum (fun i => Log (f i)) hf_sum := by
-- proof
  apply PowerSeries.Log_tprod f hf hf_sum

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_Exp_multipliable_of_summable
  [CommRing K]
  [Algebra ℚ K]
-- given
  (g : I → PowerSeries₀ (R := K))
  (hg : SummableFPS₀ g) :
-- imply
  MultipliableFPS₁ (fun i => Exp (g i)) := by
-- proof
  apply PowerSeries.Exp_multipliable_of_summable g hg

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma el_Exp_sum
  [CommRing K]
  [Algebra ℚ K]
-- given
  (g : I → PowerSeries₀ (R := K))
  (hg : SummableFPS₀ g)
  (hg_mul : MultipliableFPS₁ (fun i => Exp (g i)) := Exp_multipliable_of_summable g hg) :
-- imply
  Exp (summableFPS₀Sum g hg) = multipliableFPS₁Prod (fun i => Exp (g i)) hg_mul := by
-- proof
  apply PowerSeries.Exp_sum g hg hg_mul

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma pv_invOnePlusX_mul_one_add_X'
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  invOnePlusX K * (1 + X) = 1 := by
-- proof
  apply PowerSeries.invOnePlusX_mul_one_add_X'

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma pv_one_add_X_mul_invOnePlusX'
  [CommRing K]
  [Algebra ℚ K] :
-- imply
  (1 + X) * invOnePlusX K = 1 := by
-- proof
  apply PowerSeries.one_add_X_mul_invOnePlusX'

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma pv_coeff_mul_const_one
  [CommRing K]
  [Algebra ℚ K]
  {f g : K⟦X⟧}
  {k : ℕ}
-- given
  (hf0 : f.coeff 0 = 1)
  (hg0 : g.coeff 0 = 1)
  (hk : 1 ≤ k)
  (hf : ∀ p, 1 ≤ p → p < k → f.coeff p = 0) :
-- imply
  (f * g).coeff k = f.coeff k + g.coeff k := by
-- proof
  apply PowerSeries.coeff_mul_const_one hf0 hg0 hk hf

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma pv_coeff_eq_zero_of_not_mem_approximator
  [CommRing K]
  [Algebra ℚ K]
  [DecidableEq I]
  {f : I → K⟦X⟧}
  {n : ℕ}
  {M : Finset I}
  {i : I}
  {k : ℕ}
-- given
  (hf_const : ∀ i, constantCoeff (f i) = 1)
  (hM : ∀ m ≤ n, ∀ J : Finset I, M ⊆ J → (∏ j ∈ J, f j).coeff m = (∏ j ∈ M, f j).coeff m)
  (hi : i ∉ M)
  (hk1 : 1 ≤ k)
  (hkn : k ≤ n) :
-- imply
  (f i).coeff k = 0 := by
-- proof
  apply PowerSeries.coeff_eq_zero_of_not_mem_approximator hf_const hM hi hk1 hkn

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma pv_X_pow_dvd_pow
  [CommRing K]
  [Algebra ℚ K]
  {g : K⟦X⟧}
  {m d : ℕ}
-- given
  (h : X ^ m ∣ g)
  (hd : d ≠ 0) :
-- imply
  X ^ m ∣ g ^ d := by
-- proof
  apply PowerSeries.X_pow_dvd_pow h hd

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma pv_coeff_zero_of_X_pow_dvd
  [CommRing K]
  [Algebra ℚ K]
  {g : K⟦X⟧}
  {m n : ℕ}
-- given
  (h : X ^ m ∣ g)
  (hn : n < m) :
-- imply
  g.coeff n = 0 := by
-- proof
  apply PowerSeries.coeff_zero_of_X_pow_dvd h hn

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma pv_subst_coeff_zero_of_high_order
  [CommRing K]
  [Algebra ℚ K]
  {f g : K⟦X⟧}
  {n : ℕ}
-- given
  (hf : f.coeff 0 = 0)
  (hg : ∀ k ≤ n, g.coeff k = 0) :
-- imply
  (f.subst g).coeff (Finsupp.single () n) = 0 := by
-- proof
  apply PowerSeries.subst_coeff_zero_of_high_order hf hg

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma pv_Log_finprod
  [CommRing K]
  [Algebra ℚ K]
  [DecidableEq I]
-- given
  (f : I → PowerSeries₁ (R := K))
  (s : Finset I) :
-- imply
  Log (⟨∏ i ∈ s, (f i).val, by rw [mem_PowerSeries₁_iff, map_prod]; exact Finset.prod_eq_one (fun i _ => (f i).property)⟩) = ⟨∑ i ∈ s, (Log (f i)).val, by rw [mem_PowerSeries₀_iff, map_sum]; exact Finset.sum_eq_zero (fun i _ => (Log (f i)).property)⟩ := by
-- proof
  apply PowerSeries.Log_finprod s f

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma pv_logbar_subst_coeff_eq_of_coeff_eq
  [CommRing K]
  [Algebra ℚ K]
  {g₁ g₂ : K⟦X⟧}
  {n : ℕ}
-- given
  (hg₁ : constantCoeff g₁ = 0)
  (hg₂ : constantCoeff g₂ = 0)
  (heq : ∀ m ≤ n, g₁.coeff m = g₂.coeff m) :
-- imply
  coeff n ((logbar K).subst g₁) = coeff n ((logbar K).subst g₂) := by
-- proof
  apply PowerSeries.logbar_subst_coeff_eq_of_coeff_eq hg₁ hg₂ heq

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma pv_expbar_subst_order
  [CommRing K]
  [Algebra ℚ K]
-- given
  (g : K⟦X⟧)
  (n : ℕ)
  (hg : constantCoeff g = 0)
  (hord : n < order g) :
-- imply
  n < order ((expbar K).subst g) := by
-- proof
  apply PowerSeries.expbar_subst_order g hg n hord

/--
[ExpLog](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/ExpLog.lean)
-/
@[path]
private lemma pv_expbar_subst_coeff_zero
  [CommRing K]
  [Algebra ℚ K]
-- given
  (g : K⟦X⟧)
  (n : ℕ)
  (hg : constantCoeff g = 0)
  (hcoeff : ∀ k ≤ n, coeff k g = 0) :
-- imply
  coeff n ((expbar K).subst g) = 0 := by
-- proof
  apply PowerSeries.expbar_subst_coeff_zero g hg n hcoeff


-- created on 2026-10-23
