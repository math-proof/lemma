import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Sequences.PolynomiallyRecursiveMCFinite
open MetaMathlibExt


/--
[isMCFinite_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Sequences/PolynomiallyRecursiveMCFinite.lean)
-/
@[path]
private lemma isMCFinite_iff_eq
  {s : ℕ → ℤ} :
-- imply
  IsMCFinite s ↔ ∀ m : ℕ, 0 < m →
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
    ∃ c : Fin p → ℤ, ∀ n : ℕ, q ≤ n →
    (s (n + p) - ∑ i : Fin p, c i * s (n + i.val)) % (↑m : ℤ) = 0 := by
-- proof
  apply MetaMathlibExt.isMCFinite_iff s

/--
[isMCFinite_of_mvPolynomial_recursion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Sequences/PolynomiallyRecursiveMCFinite.lean)
-/
@[path]
private lemma isMCFinite_of_mvPolynomial_recursion_eq
  {k : ℕ}
  {u : Fin (k + 1) → ℕ → ℤ}
  {P : Fin (k + 1) → MvPolynomial (Fin (k + 1) ⊕ Unit) ℤ}
-- given
  (hrec : ∀ i : Fin (k + 1), ∀ n : ℕ, u i (n + 1) = MvPolynomial.eval (Sum.elim (fun j : Fin (k + 1) => u j n) (fun _ : Unit => (↑n : ℤ))) (P i)) :
-- imply
  IsMCFinite (u 0) := by
-- proof
  apply MetaMathlibExt.isMCFinite_of_mvPolynomial_recursion u P hrec

/--
[IsPRecursiveSequence.isMCFinite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Sequences/PolynomiallyRecursiveMCFinite.lean)
-/
@[path]
private lemma IsPRecursiveSequence_isMCFinite_eq
  {k : ℕ}
  {Q : Fin (k + 1) → Polynomial ℤ}
  {s : ℕ → ℤ}
-- given
  (hs : IsPRecursiveSequence k Q s)
  (hQ : Q 0 = 1) :
-- imply
  IsMCFinite s := by
-- proof
  apply MetaMathlibExt.IsPRecursiveSequence.isMCFinite hs hQ

/--
[polynomially_recursive_MC_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Sequences/PolynomiallyRecursiveMCFinite.lean)
-/
@[path]
private lemma polynomially_recursive_MC_finite_eq
  {s : ℕ → ℤ} :
-- imply
  ((∃ k : ℕ, ∃ u : Fin (k + 1) → ℕ → ℤ,
    ∃ P : Fin (k + 1) → MvPolynomial (Fin (k + 1) ⊕ Unit) ℤ,
    s = u 0 ∧
    ∀ i : Fin (k + 1), ∀ n : ℕ,
    u i (n + 1) = MvPolynomial.eval
    (Sum.elim (fun j : Fin (k + 1) => u j n) (fun _ : Unit => (↑n : ℤ))) (P i)) →
    ∀ m : ℕ, 0 < m →
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
    ∃ c : Fin p → ℤ, ∀ n : ℕ, q ≤ n →
    (s (n + p) - ∑ i : Fin p, c i * s (n + i.val)) % (↑m : ℤ) = 0) ∧
    ((∃ k : ℕ, ∃ P : ℕ → Polynomial ℤ,
    0 < k ∧ P 1 ≠ 0 ∧ P k ≠ 0 ∧
    ∀ n : ℕ, k ≤ n →
    s n = ∑ i : Fin k, (P (i.val + 1)).eval (↑n : ℤ) * s (n - (i.val + 1))) →
    ∀ m : ℕ, 0 < m →
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
    ∃ c : Fin p → ℤ, ∀ n : ℕ, q ≤ n →
    (s (n + p) - ∑ i : Fin p, c i * s (n + i.val)) % (↑m : ℤ) = 0) := by
-- proof
  apply MetaMathlibExt.polynomially_recursive_MC_finite s


-- created on 2026-10-20
