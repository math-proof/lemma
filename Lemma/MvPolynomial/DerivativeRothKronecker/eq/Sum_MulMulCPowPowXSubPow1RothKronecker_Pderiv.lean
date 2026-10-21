import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothKronecker_derivative](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [Field K] (D : ℕ)
  (P : MvPolynomial (Fin m) K) :
-- imply
  (rothKronecker D P).derivative =
    ∑ h : Fin m,
      Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
        rothKronecker D (MvPolynomial.pderiv h P) := by
-- proof
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp [rothKronecker]
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _
    ring
  | mul_X P n hP =>
    have hsecond :
      (∑ h : Fin m,
          Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
            ((rothKronecker D P) *
              rothKronecker D (MvPolynomial.pderiv h (MvPolynomial.X n)))) =
        Polynomial.C (D ^ (n : ℕ) : K) * Polynomial.X ^ (D ^ (n : ℕ) - 1) *
          rothKronecker D P := by
      rw [Finset.sum_eq_single n]
      ·
        simp [mul_assoc, mul_comm]
      ·
        intro h _ hne
        rw [MvPolynomial.pderiv_X_of_ne hne.symm]
        simp
      ·
        simp
    have hX :
      rothKronecker D (MvPolynomial.X n : MvPolynomial (Fin m) K) =
        Polynomial.X ^ D ^ (n : ℕ) := by
      simp [rothKronecker]
    rw [map_mul, hX, Polynomial.derivative_mul, hP, Polynomial.derivative_X_pow]
    symm
    calc
      _ = ∑ h : Fin m,
            (Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
                rothKronecker D (MvPolynomial.pderiv h P) *
                  Polynomial.X ^ D ^ (n : ℕ) +
              Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
                ((rothKronecker D P) *
                  rothKronecker D (MvPolynomial.pderiv h (MvPolynomial.X n)))) := by
        apply Finset.sum_congr rfl
        intro h _
        rw [MvPolynomial.pderiv_mul]
        simp only [map_add, map_mul, hX]
        ring
      _ = (∑ h : Fin m,
              Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
                rothKronecker D (MvPolynomial.pderiv h P) *
                  Polynomial.X ^ D ^ (n : ℕ)) +
            ∑ h : Fin m,
              Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
                ((rothKronecker D P) *
                  rothKronecker D (MvPolynomial.pderiv h (MvPolynomial.X n))) :=
        Finset.sum_add_distrib
      _ = (∑ h : Fin m,
              Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
                rothKronecker D (MvPolynomial.pderiv h P)) *
              Polynomial.X ^ D ^ (n : ℕ) +
            Polynomial.C (D ^ (n : ℕ) : K) * Polynomial.X ^ (D ^ (n : ℕ) - 1) *
              rothKronecker D P := by
        rw [← Finset.sum_mul, hsecond]
      _ = _ := by
        push_cast
        ring


-- created on 2026-10-21
