/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean -/

import Def.NumberTheory.Cyclotomic.RealCyclotomicPolynomial
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Def.NumberTheory.Cyclotomic.LehmerLaurentIdentity.Part2


namespace MetaMathlibExt

/-- `R = Φₙ`. -/
lemma clearPoly_eq (n : ℕ) (hn : 2 < n) :
    clearPoly n = Polynomial.cyclotomic n ℤ := by
  have hζ := zeta_isPrimitiveRoot n (by omega)
  have hP : Polynomial.cyclotomic n ℤ = minpoly ℤ (zeta n) :=
    Polynomial.cyclotomic_eq_minpoly hζ (by omega)
  have hdvd : Polynomial.cyclotomic n ℤ ∣ clearPoly n := by
    rw [hP]
    apply minpoly.isIntegrallyClosed_dvd (zeta_isIntegral n (by omega))
    exact clearPoly_aeval n
  have hdegP : (Polynomial.cyclotomic n ℤ).natDegree = n.totient :=
    Polynomial.natDegree_cyclotomic n ℤ
  have he := natDegree_psi_eq n hn
  have hRdeg := clearPoly_natDegree n hn
  have hle : (clearPoly n).natDegree ≤ (Polynomial.cyclotomic n ℤ).natDegree := by
    rw [hRdeg, hdegP, he]
    obtain ⟨d, hd⟩ := Nat.totient_even hn
    omega
  have h := Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (Polynomial.cyclotomic.monic n ℤ) (clearPoly_monic n hn) hdvd hle
  exact h

/-- Laurent transfer: `toLaurent R = T^d · ψ(T + T⁻¹)`. -/
lemma transfer (n : ℕ) (hn : 2 < n) :
    Polynomial.toLaurent (clearPoly n)
      = LaurentPolynomial.T (((n.totient / 2 : ℕ)) : ℤ)
        * Polynomial.aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1))
          (minpoly ℤ (zeta n + (zeta n)⁻¹)) := by
  have hTS : (LaurentPolynomial.T (2 : ℤ) + 1 : LaurentPolynomial ℤ)
      = (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
        * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
          + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) := by
    have h2 : (LaurentPolynomial.T (2 : ℤ) : LaurentPolynomial ℤ)
        = (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
          * (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ) := by
      have h22 : (2 : ℤ) = 1 + 1 := by norm_num
      rw [h22, LaurentPolynomial.T_add]
    have h10 : (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
          * (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)
        = (1 : LaurentPolynomial ℤ) := by
      have h00 : (1 : ℤ) + (-1) = 0 := by norm_num
      have hT : (LaurentPolynomial.T ((1 : ℤ) + (-1)) : LaurentPolynomial ℤ)
          = (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
            * (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ) :=
        LaurentPolynomial.T_add (1 : ℤ) (-1)
      rw [h00, LaurentPolynomial.T_zero] at hT
      exact hT.symm
    rw [h2, ← h10, mul_add]
  have hT1k : ∀ k : ℕ, ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ) ^ k
      = (LaurentPolynomial.T ((((k : ℕ))) : ℤ) : LaurentPolynomial ℤ)) := by
    intro k
    rw [LaurentPolynomial.T_pow, mul_one]
  unfold clearPoly
  set e := (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree with he
  have hed : e = n.totient / 2 := by
    rw [he]
    exact natDegree_psi_eq n hn
  have hcast : ∀ k : ℕ, k ≤ e →
      ((((e - k : ℕ))) : ℤ) + ((((k : ℕ))) : ℤ) = ((((e : ℕ))) : ℤ) := by
    intro k hke
    rw [← Nat.cast_add]
    congr 1
    omega
  have hterm : ∀ k : ℕ, k ≤ e →
      (LaurentPolynomial.T ((((e - k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
        * ((LaurentPolynomial.T (2 : ℤ) : LaurentPolynomial ℤ) + 1) ^ k
      = (LaurentPolynomial.T ((((n.totient / 2 : ℕ))) : ℤ) : LaurentPolynomial ℤ)
        * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
          + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k := by
    intro k hke
    calc (LaurentPolynomial.T ((((e - k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
            * ((LaurentPolynomial.T (2 : ℤ) : LaurentPolynomial ℤ) + 1) ^ k
        = (LaurentPolynomial.T ((((e - k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
          * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
            * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
              + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ))) ^ k := by
          rw [hTS]
      _ = (LaurentPolynomial.T ((((e - k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
          * (((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)) ^ k
            * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
              + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k) := by
          rw [mul_pow]
      _ = (LaurentPolynomial.T ((((e - k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
          * ((LaurentPolynomial.T ((((k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
            * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
              + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k) := by
          rw [hT1k k]
      _ = ((LaurentPolynomial.T ((((e - k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
            * (LaurentPolynomial.T ((((k : ℕ))) : ℤ) : LaurentPolynomial ℤ))
          * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
            + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k := by
          ring
      _ = (LaurentPolynomial.T (((((e - k : ℕ))) : ℤ) + ((((k : ℕ))) : ℤ)) :
              LaurentPolynomial ℤ)
          * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
            + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k := by
          rw [← LaurentPolynomial.T_add]
      _ = (LaurentPolynomial.T ((((e : ℕ))) : ℤ) : LaurentPolynomial ℤ)
          * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
            + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k := by
          rw [hcast k hke]
      _ = (LaurentPolynomial.T ((((n.totient / 2 : ℕ))) : ℤ) : LaurentPolynomial ℤ)
          * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
            + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k := by
          rw [hed]
  have haeval : Polynomial.aeval
      ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
        + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ))
      (minpoly ℤ (zeta n + (zeta n)⁻¹))
      = ∑ k ∈ Finset.range (e + 1),
        LaurentPolynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
        * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
          + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k := by
    have h := Polynomial.as_sum_range_C_mul_X_pow (minpoly ℤ (zeta n + (zeta n)⁻¹))
    have h2 := congrArg
      (Polynomial.aeval ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
        + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ))) h
    simp only [map_sum, Polynomial.aeval_C, map_mul, map_pow, Polynomial.aeval_X,
      ← LaurentPolynomial.C_eq_algebraMap] at h2
    rw [← he] at h2
    rw [← h2]
  rw [map_sum, haeval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hke : k ≤ e := by
    have hmem := Finset.mem_range.mp hk
    omega
  simp only [map_mul, map_pow, map_add, map_one, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X]
  have h2' : ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ) ^ 2
      = (LaurentPolynomial.T (2 : ℤ) : LaurentPolynomial ℤ)) := by
    simpa only [Nat.cast_ofNat] using hT1k 2
  rw [hT1k (e - k), h2', hterm k hke]
  ring

/-- Denominator-cleared Laurent-polynomial form of `ψₙ(x + x⁻¹) = x^(-φ(n)/2) Φₙ(x)`:
multiplying the evaluation of the real cyclotomic polynomial at `x + x⁻¹` by
`x ^ (φ(n) / 2)` recovers the cyclotomic polynomial as a Laurent polynomial.

Source: Pinthira Tangsupphathawat and Vichian Laohakosol, "Minimal Polynomials of
Algebraic Cosine Values at Rational Multiples of π", Journal of Integer Sequences 19
(2016), source lines 83-90:
https://cs.uwaterloo.ca/journals/JIS/VOL19/Laohakosol/lao2.tex
source SHA-256 15e6923301658b132cd14eb587f480152fbf9dd9554ecbc6ce321216d9314455
normalized no-final-newline span SHA-256
e91ccd0347f84043d402747f2c4aaf5e6d5f22cba3840369c7fb8a8732dbe039

Proves `Wanted` entry `lehmer_cyclotomic_identity`.
-/
theorem lehmer_cyclotomic_identity (n : ℕ) (hn : 2 < n) :
    LaurentPolynomial.T (↑(n.totient / 2)) *
      Polynomial.aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1))
        (realCyclotomicPolynomial n) =
      Polynomial.toLaurent (Polynomial.cyclotomic n ℤ) := by
  have hR := clearPoly_eq n hn
  have htrans := transfer n hn
  have hdef : realCyclotomicPolynomial n
      = minpoly ℤ (zeta n + (zeta n)⁻¹) := rfl
  rw [hdef, ← hR]
  exact htrans.symm

end MetaMathlibExt
