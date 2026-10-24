/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Sequences/PolynomiallyRecursiveMCFinite.lean -/


import Mathlib.Tactic
import sympy.atlas.NumberTheory.Sequences.PolynomiallyRecursiveMCFinite
import Lemma.Nat.Sequences.PolynomiallyRecursiveMCFinite


namespace MathlibExtTest.NumberTheory.Sequences.PolynomiallyRecursiveMCFinite

open MetaMathlibExt MvPolynomial

example : IsMCFinite (fun _ => 1) :=
  fun _ _ => ⟨1, 1, one_pos, one_pos, fun _ => 1, fun _ _ => by simp⟩

/-- `a (n + 1) = a n * b n + n`, `b (n + 1) = b n + 1`, starting from `(1, 1)`. -/
def coupledPair : ℕ → ℤ × ℤ
  | 0 => (1, 1)
  | n + 1 => ((coupledPair n).1 * (coupledPair n).2 + n, (coupledPair n).2 + 1)

example : IsMCFinite fun n => (coupledPair n).1 := by
  refine isMCFinite_of_mvPolynomial_recursion (k := 1)
    ![fun n => (coupledPair n).1, fun n => (coupledPair n).2]
    ![X (.inl 0) * X (.inl 1) + X (.inr ()), X (.inl 1) + 1] fun i n => ?_
  fin_cases i <;> simp [coupledPair]

example : IsMCFinite fun _ => 0 :=
  IsPRecursiveSequence.isMCFinite (k := 0) (Q := fun _ => 1) (fun _ _ => by simp) rfl

example : IsMCFinite fun n => (n.factorial : ℤ) := by
  refine IsPRecursiveSequence.isMCFinite (k := 1) (Q := ![1, Polynomial.X]) ?_ rfl
  rintro (_ | n) hn
  · simp at hn
  · simp [Nat.factorial_succ]

example : IsMCFinite fun n => (Nat.fib n : ℤ) := by
  refine IsPRecursiveSequence.isMCFinite (k := 2) (Q := ![1, 1, 1]) ?_ rfl
  rintro (_ | _ | n) hn
  · simp at hn
  · simp at hn
  · simp [Fin.sum_univ_two, Nat.fib_add_two]
    ring

end MathlibExtTest.NumberTheory.Sequences.PolynomiallyRecursiveMCFinite
