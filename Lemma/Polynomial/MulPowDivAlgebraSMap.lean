import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[RatFunc_X_zpow_mul_div_eq_of_forall_lt_re_mul_eval_cpow_neg_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RatFunc_X_zpow_mul_div_eq_of_forall_lt_re_mul_eval_cpow_neg_eq.lean)
-/
@[path]
private lemma main
  (N : ℕ) (hN : 1 < N) (σ : ℝ) (f : ℂ → ℂ)
  (P Q P' Q' : Polynomial ℂ) (m m' : ℤ) (hQ : Q ≠ 0) (hQ' : Q' ≠ 0)
  (h : ∀ s : ℂ, σ < s.re → f s * Q.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)))
  (h' : ∀ s : ℂ, σ < s.re → f s * Q'.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m' : ℂ) * s) * P'.eval ((N : ℂ) ^ (-s))) :
  -- imply
  (RatFunc.X : RatFunc ℂ) ^ (-m) * (algebraMap (Polynomial ℂ) (RatFunc ℂ) P / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q) =
    (RatFunc.X : RatFunc ℂ) ^ (-m') * (algebraMap (Polynomial ℂ) (RatFunc ℂ) P' / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q') := by
  -- proof
  classical
  have hN0 : (N : ℂ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN
  set e : ℕ := (m' - m).toNat with he
  set e' : ℕ := (m - m').toNat with he'
  set M : ℤ := max m m' with hM
  have hMe : (M : ℤ) - m = e := by
    rw [he, hM]
    obtain hle | hle := le_total m m'
    ·
      rw [max_eq_right hle, Int.toNat_of_nonneg (sub_nonneg.2 hle)]
    ·
      rw [max_eq_left hle, sub_self, Int.toNat_of_nonpos (sub_nonpos.2 hle)]
      simp
  have hMe' : (M : ℤ) - m' = e' := by
    rw [he', hM]
    obtain hle | hle := le_total m m'
    ·
      rw [max_eq_right hle, sub_self, Int.toNat_of_nonpos (sub_nonpos.2 hle)]
      simp
    ·
      rw [max_eq_left hle, Int.toNat_of_nonneg (sub_nonneg.2 hle)]
  have hx : ∀ (k : ℤ) (n : ℕ) (t : ℝ), (M : ℤ) - k = n → (N : ℂ) ^ ((k : ℂ) * (t : ℂ)) * (N : ℂ) ^ (-((M : ℂ) * (t : ℂ))) = ((N : ℂ) ^ (-(t : ℂ))) ^ n := by
    intro k n t hk
    rw [← Complex.cpow_add _ _ hN0, ← Complex.cpow_nat_mul]
    congr 1
    have hnk : (n : ℂ) = (M : ℂ) - (k : ℂ) := by
      exact_mod_cast hk.symm
    rw [hnk]
    ring
  have hA : ∀ t : ℝ, σ < t → (Polynomial.X ^ e * (P * Q')).eval ((N : ℂ) ^ (-(t : ℂ))) = (Polynomial.X ^ e' * (P' * Q)).eval ((N : ℂ) ^ (-(t : ℂ))) := by
    intro t ht
    have ht' : σ < ((t : ℂ)).re := by
      simpa using ht
    have h1 := h (t : ℂ) ht'
    have h2 := h' (t : ℂ) ht'
    have key : (N : ℂ) ^ ((m : ℂ) * (t : ℂ)) * P.eval ((N : ℂ) ^ (-(t : ℂ))) * Q'.eval ((N : ℂ) ^ (-(t : ℂ))) = (N : ℂ) ^ ((m' : ℂ) * (t : ℂ)) * P'.eval ((N : ℂ) ^ (-(t : ℂ))) * Q.eval ((N : ℂ) ^ (-(t : ℂ))) := by
      rw [← h1]
      ring
      rw [h2]
    have key2 := congrArg (fun z => z * (N : ℂ) ^ (-((M : ℂ) * (t : ℂ)))) key
    have l1 := hx m e t hMe
    have l2 := hx m' e' t hMe'
    simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    calc
      _ = ((N : ℂ) ^ ((m : ℂ) * (t : ℂ)) * P.eval ((N : ℂ) ^ (-(t : ℂ))) * Q'.eval ((N : ℂ) ^ (-(t : ℂ)))) * (N : ℂ) ^ (-((M : ℂ) * (t : ℂ))) := by
        rw [← l1]
        ring
      _ = ((N : ℂ) ^ ((m' : ℂ) * (t : ℂ)) * P'.eval ((N : ℂ) ^ (-(t : ℂ))) * Q.eval ((N : ℂ) ^ (-(t : ℂ)))) * (N : ℂ) ^ (-((M : ℂ) * (t : ℂ))) := key2
      _ = ((N : ℂ) ^ (-(t : ℂ))) ^ e' * (P'.eval ((N : ℂ) ^ (-(t : ℂ))) * Q.eval ((N : ℂ) ^ (-(t : ℂ)))) := by
        rw [← l2]
        ring
  have hinj : Function.Injective fun t : ℝ => (N : ℂ) ^ (-(t : ℂ)) := by
    intro t₁ t₂ ht
    have e1 : ∀ t : ℝ, (N : ℂ) ^ (-(t : ℂ)) = (((N : ℝ) ^ (-t) : ℝ) : ℂ) := by
      intro t
      rw [Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ (N : ℝ))]
      push_cast
      rfl
    simp [e1] at ht
    have ht2 : (N : ℝ) ^ (-t₁) = (N : ℝ) ^ (-t₂) := by
      exact_mod_cast ht
    have hmono : StrictMono fun t : ℝ => (N : ℝ) ^ t := fun a b hab => (Real.rpow_lt_rpow_left_iff hN1).2 hab
    have := hmono.injective ht2
    linarith
  have hB : Polynomial.X ^ e * (P * Q') = Polynomial.X ^ e' * (P' * Q) := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := (fun t : ℝ => (N : ℂ) ^ (-(t : ℂ))) '' Set.Ioi σ) ?_ ?_
    ·
      intro x hx
      obtain ⟨t, ht, rfl⟩ := hx
      apply hA t ht
    ·
      apply (Set.Ioi_infinite σ).image hinj.injOn
  have hXne : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have hQr : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q ≠ 0 := RatFunc.algebraMap_ne_zero hQ
  have hQr' : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q' ≠ 0 := RatFunc.algebraMap_ne_zero hQ'
  have hBr := congrArg (algebraMap (Polynomial ℂ) (RatFunc ℂ)) hB
  simp [map_mul, map_pow, RatFunc.algebraMap_X] at hBr
  rw [mul_div_assoc', mul_div_assoc', div_eq_div_iff hQr hQr']
  apply mul_left_cancel₀ (zpow_ne_zero M hXne)
  calc
    _ = (RatFunc.X : RatFunc ℂ) ^ (M + -m) * algebraMap (Polynomial ℂ) (RatFunc ℂ) P * algebraMap (Polynomial ℂ) (RatFunc ℂ) Q' := by
      rw [zpow_add₀ hXne]
      ring
    _ = (RatFunc.X : RatFunc ℂ) ^ e * (algebraMap (Polynomial ℂ) (RatFunc ℂ) P * algebraMap (Polynomial ℂ) (RatFunc ℂ) Q') := by
      rw [show M + -m = (e : ℤ) by omega, zpow_natCast]
      ring
    _ = (RatFunc.X : RatFunc ℂ) ^ e' * (algebraMap (Polynomial ℂ) (RatFunc ℂ) P' * algebraMap (Polynomial ℂ) (RatFunc ℂ) Q) := hBr
    _ = (RatFunc.X : RatFunc ℂ) ^ (M + -m') * algebraMap (Polynomial ℂ) (RatFunc ℂ) P' * algebraMap (Polynomial ℂ) (RatFunc ℂ) Q := by
      rw [show M + -m' = (e' : ℤ) by omega, zpow_natCast]
      ring
    _ = (RatFunc.X : RatFunc ℂ) ^ M * ((RatFunc.X : RatFunc ℂ) ^ (-m') * algebraMap (Polynomial ℂ) (RatFunc ℂ) P' * algebraMap (Polynomial ℂ) (RatFunc ℂ) Q) := by
      rw [zpow_add₀ hXne]
      ring


-- created on 2026-10-20
