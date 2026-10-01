import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma independence.vector
  {n : ℕ}
  {x y : Fin n → ℂ}
-- given
  (h : ∀ p : ℂ, p ≠ 0 → ∑ k : Fin n, p ^ (k : ℕ) * x k = ∑ k : Fin n, p ^ (k : ℕ) * y k) :
-- imply
  x = y := by
-- proof
  set P : Polynomial ℂ := ∑ k : Fin n, Polynomial.C (x k - y k) * Polynomial.X ^ (k : ℕ) with hP
  have hroot : ({0}ᶜ : Set ℂ) ⊆ {p | P.IsRoot p} := by
    intro p hp
    have hp' : p ≠ 0 := hp
    show Polynomial.eval p P = 0
    rw [hP, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    have := h p hp'
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at this
    rw [← this]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hinf : Set.Infinite ({0}ᶜ : Set ℂ) := (Set.finite_singleton (0 : ℂ)).infinite_compl
  have hP0 : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P (hinf.mono hroot)
  funext k
  have hc := congrArg (fun q => Polynomial.coeff q (k : ℕ)) hP0
  simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single k (fun j _ hj => if_neg (fun e => hj (Fin.ext e.symm))) (fun hk => absurd (Finset.mem_univ k) hk), if_pos rfl] at hc
  exact sub_eq_zero.mp hc


@[main]
private lemma independence.matrix
  {n m : ℕ}
  {x y : Fin n → Fin m → ℂ}
-- given
  (h : ∀ p : ℂ, p ≠ 0 → ∀ j, ∑ k : Fin n, p ^ (k : ℕ) * x k j = ∑ k : Fin n, p ^ (k : ℕ) * y k j) :
-- imply
  x = y := by
-- proof
  funext k j
  exact congrFun (independence.vector (x := fun k => x k j) (y := fun k => y k j) (fun p hp => h p hp j)) k


-- created on 2026-09-27
