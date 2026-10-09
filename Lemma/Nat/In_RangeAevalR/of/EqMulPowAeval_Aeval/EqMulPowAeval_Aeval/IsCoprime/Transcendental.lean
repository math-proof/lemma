import Mathlib
import sympy.Basic


/--
[Polynomial_mem_range_aeval_of_isCoprime_of_pow_mul_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_mem_range_aeval_of_isCoprime_of_pow_mul_eq.lean)
-/
@[path]
private lemma main
  {F A : Type*} [Field F] [CommRing A] [IsDomain A] [Algebra F A]
  {x : A}
  {f g : Polynomial F}
  {z : A}
  {m n : ℕ}
  {P Q : Polynomial F}
-- given
  (hx : Transcendental F x)
  (hfg : IsCoprime f g)
  (hf : Polynomial.aeval x f ^ m * z = Polynomial.aeval x P)
  (hg : Polynomial.aeval x g ^ n * z = Polynomial.aeval x Q) :
-- imply
  z ∈ (Polynomial.aeval (R :=
-- proof
  F) x).range := by
   have hinj : Function.Injective (Polynomial.aeval (R := F) x) := transcendental_iff_injective.mp hx

   have key : P * g ^ n = Q * f ^ m := by
     apply hinj
     rw [map_mul, map_pow, map_mul, map_pow, ← hf, ← hg]
     ring
   have hdvd : f ^ m ∣ P := by
     have hcop : IsCoprime (f ^ m) (g ^ n) := hfg.pow
     exact hcop.dvd_of_dvd_mul_right ⟨Q, by rw [key]; ring⟩
   obtain ⟨P', hP'⟩ := hdvd
   by_cases h0 : Polynomial.aeval x f ^ m = 0
   ·
     have hfm : f ^ m = 0 := hinj (by rw [map_pow, h0, map_zero])
     have hf0 : f = 0 := pow_eq_zero_iff (n := m) (by rintro rfl; rw [pow_zero] at hfm; exact one_ne_zero hfm) |>.mp hfm
     rw [hf0, isCoprime_zero_left] at hfg
     obtain ⟨c, hc, hcg⟩ := Polynomial.isUnit_iff.mp hfg
     have hgn : Polynomial.aeval x g ^ n = algebraMap F A (c ^ n) := by
       rw [← hcg, Polynomial.aeval_C, map_pow]
     rw [hgn] at hg
     have hcn : c ^ n ≠ 0 := pow_ne_zero _ hc.ne_zero
     refine ⟨Polynomial.C (c ^ n)⁻¹ * Q, ?_⟩
     show Polynomial.aeval x (Polynomial.C (c ^ n)⁻¹ * Q) = z
     rw [map_mul, Polynomial.aeval_C, ← hg, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hcn, map_one, one_mul]
   · refine ⟨P', ?_⟩
     show Polynomial.aeval x P' = z
     apply mul_left_cancel₀ h0
     rw [hf, hP', map_mul, map_pow]


-- created on 2026-10-05
