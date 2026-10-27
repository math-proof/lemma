import Mathlib
import Initialize.Tactic.Attr.Basic


/--
py stated that equality of two power series (with no convergence hypothesis) forces equality of
all coefficients. A radius is needed: if both series are absolutely convergent at `ρ > 0` and
agree for every `|x| < ρ`, then `A n = B n` for all `n`.
-/
@[path]
private lemma main
  {A B : ℕ → ℝ}
  {ρ : ℝ}
-- given
  (hρ : 0 < ρ)
  (hsA : Summable (fun n => |A n| * ρ ^ n))
  (hsB : Summable (fun n => |B n| * ρ ^ n))
  (heq : ∀ x : ℝ, |x| < ρ → ∑' n, A n * x ^ n = ∑' n, B n * x ^ n) :
-- imply
  A = B := by
-- proof
  let c : ℕ → ℝ := fun n => A n - B n
  have h1c : ∀ n, |c n| ≤ |A n| + |B n| := by
    intro n
    have h : c n = A n - B n := rfl
    rw [h]
    have hn : ‖A n - B n‖ ≤ ‖A n‖ + ‖-B n‖ := norm_add_le (A n) (-B n)
    simpa using hn
  have hcs : Summable (fun n => |c n| * ρ ^ n) := by
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hsA.add hsB)
    intro n
    have h2 : |c n| * ρ ^ n ≤ (|A n| + |B n|) * ρ ^ n :=
      mul_le_mul (h1c n) le_rfl (by positivity) (by positivity)
    rwa [show (|A n| + |B n|) * ρ ^ n = |A n| * ρ ^ n + |B n| * ρ ^ n by ring] at h2
  have hmaj : ∀ (d : ℕ → ℝ) (x : ℝ), |x| < ρ → Summable (fun n => |d n| * ρ ^ n) →
      Summable (fun n => d n * x ^ n) := by
    intro d x hxρ hd
    have h4 : ∀ n, |d n * x ^ n| ≤ |d n| * ρ ^ n := by
      intro n
      have h6 : |x| ^ n ≤ ρ ^ n := by gcongr
      simpa [abs_mul, abs_pow] using mul_le_mul_of_nonneg_left h6 (abs_nonneg (d n))
    apply Summable.of_norm
    exact Summable.of_nonneg_of_le (fun _ => by positivity) h4 hd
  have htail_summable : ∀ (k : ℕ) (x : ℝ), x ≠ 0 → |x| < ρ →
      Summable (fun j => c (k + 1 + j) * x ^ j) := by
    intro k x hx0 hxρ
    apply (summable_mul_left_iff (pow_ne_zero (k + 1) hx0)).mp
    rw [show (fun j : ℕ => x ^ (k + 1) * (c (k + 1 + j) * x ^ j)) =
        fun j => c (j + (k + 1)) * x ^ (j + (k + 1)) from funext fun j => by ring_nf]
    exact (summable_nat_add_iff (f := fun n => c n * x ^ n) (k + 1)).mpr
      (hmaj c x hxρ hcs)
  have hcoef : ∀ k, (∀ i < k, c i = 0) → c k = 0 := by
    intro k hprev
    have htailρ : Summable (fun j => |c (k + 1 + j)| * ρ ^ j) := by
      apply (summable_mul_left_iff (a := ρ ^ (k + 1))
        (f := fun j => |c (k + 1 + j)| * ρ ^ j) (pow_ne_zero _ hρ.ne')).mp
      convert (summable_nat_add_iff (f := fun n => |c n| * ρ ^ n) (k + 1)).mpr hcs using 1
      funext j
      ring_nf
    set M : ℝ := ∑' j, |c (k + 1 + j)| * ρ ^ j with hM
    have hMnonneg : 0 ≤ M := tsum_nonneg fun _ => by positivity
    have h_eq : ∀ (x : ℝ), x ≠ 0 → |x| < ρ →
        c k + x * (∑' j, c (k + 1 + j) * x ^ j) = 0 := by
      intro x hx0 hxρ
      have hsxA := hmaj A x hxρ hsA
      have hsxB := hmaj B x hxρ hsB
      have hsx := hmaj c x hxρ hcs
      have h0 : ∑' n, c n * x ^ n = 0 := by
        have hce : (fun n => c n * x ^ n) = fun n => A n * x ^ n - B n * x ^ n := by
          funext n
          simp [c]; ring
        rw [hce]
        exact (hsxA.tsum_sub hsxB).trans (by rw [heq x hxρ, sub_self])
      have hsplit : (∑ i ∈ Finset.range k, c i * x ^ i) + ∑' j, c (j + k) * x ^ (j + k) =
          ∑' n, c n * x ^ n := hsx.sum_add_tsum_nat_add k
      have hr0 : ∑ i ∈ Finset.range k, c i * x ^ i = 0 := by
        rw [Finset.sum_eq_zero]
        intro i hi
        rw [hprev i (Finset.mem_range.mp hi), zero_mul]
      have hst : Summable (fun j => c (j + k) * x ^ j) := by
        apply (summable_mul_left_iff (pow_ne_zero k hx0)).mp
        rw [show (fun j : ℕ => x ^ k * (c (j + k) * x ^ j)) =
            fun j => c (j + k) * x ^ (j + k) from funext fun j => by ring]
        exact (summable_nat_add_iff (f := fun n => c n * x ^ n) k).mpr hsx
      have htail0 : ∑' j, c (j + k) * x ^ (j + k) = 0 := by
        linarith [hr0, hsplit, h0]
      have hconv : (fun j => c (j + k) * x ^ (j + k)) =
          fun j => x ^ k * (c (j + k) * x ^ j) := by
        funext j
        ring
      have hT := htail_summable k x hx0 hxρ
      set Tv : ℝ := ∑' j, c (k + 1 + j) * x ^ j with hTv
      have h12 : ∑' j, c (j + k) * x ^ j = c k + x * Tv := by
        have hz := hst.tsum_eq_zero_add
        have hfirst : c (0 + k) * x ^ 0 = c k := by simp
        have hrest : ∑' b, c (b + 1 + k) * x ^ (b + 1) = x * Tv := by
          have hconv : (fun b : ℕ => c (b + 1 + k) * x ^ (b + 1)) =
              fun b => x * (c (k + 1 + b) * x ^ b) := by
            funext b
            ring_nf
          rw [hconv, hT.tsum_mul_left x]
        rw [hz, hfirst, hrest]
      rw [hconv, hst.tsum_mul_left (x ^ k)] at htail0
      rw [h12] at htail0
      exact (mul_eq_zero.mp htail0).resolve_left (pow_ne_zero k hx0)
    have hbd : ∀ (x : ℝ), x ≠ 0 → |x| < ρ → |c k| ≤ |x| * M := by
      intro x hx0 hxρ
      have hT := htail_summable k x hx0 hxρ
      set Tv : ℝ := ∑' j, c (k + 1 + j) * x ^ j with hTv
      have h13 := h_eq x hx0 hxρ
      have h14 : c k = -(x * Tv) := by linarith
      have h15 : Summable (fun j => |c (k + 1 + j) * x ^ j|) := hT.norm
      have h16 : |Tv| ≤ ∑' j, |c (k + 1 + j) * x ^ j| :=
        norm_tsum_le_tsum_norm (f := fun j => c (k + 1 + j) * x ^ j) h15
      calc
        _ = |x| * |Tv| := by rw [h14, abs_neg, abs_mul]
        _ ≤ |x| * M := by
          gcongr
          exact h16.trans (h15.tsum_le_tsum (fun j => by
            have h20 : |x| ^ j ≤ ρ ^ j := by gcongr
            simpa [abs_mul, abs_pow] using
              mul_le_mul_of_nonneg_left h20 (abs_nonneg _)) htailρ)
    have hsmall : ∀ ε, 0 < ε → |c k| < ε := by
      intro ε hε
      set y : ℝ := min (ρ / 2) (ε / (M + 1)) with hy
      have hy0 : 0 < y := lt_min (by linarith) (div_pos hε (by linarith))
      have hyρ : y < ρ := calc
        _ ≤ ρ / 2 := min_le_left _ _
        _ < ρ := by linarith
      have h21 : |c k| ≤ y * M := by
        have hya : |y| = y := abs_of_pos hy0
        have h := hbd y hy0.ne' (by rwa [hya])
        simpa [hya] using h
      have h22 : M * y < ε := by
        have h23 : M * y ≤ M * (ε / (M + 1)) := by gcongr; exact min_le_right _ _
        have h24 : M * (ε / (M + 1)) = (M / (M + 1)) * ε := by ring
        rw [h24] at h23
        have h25 : M / (M + 1) < 1 := by
          apply (div_lt_one (by linarith)).mpr
          linarith
        nlinarith
      linarith
    if h : c k = 0 then
      exact h
    else
      have h27 : 0 < |c k| := abs_pos.mpr h
      have h28 := hsmall (|c k|) h27
      linarith
  have hall : ∀ k, ∀ i < k, c i = 0 := by
    intro k
    induction k with
    | zero =>
      intro i hi
      exact False.elim (Nat.not_lt_zero i hi)
    | succ m ih =>
      intro i hi
      if hik : i = m then
        rw [hik]
        exact hcoef m ih
      else
        exact ih i (by omega)
  funext n
  exact sub_eq_zero.mp (hcoef n (hall n))


-- created on 2020-05-18
