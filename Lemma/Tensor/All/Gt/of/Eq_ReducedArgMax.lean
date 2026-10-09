import sympy.concrete.reduced
import sympy.Basic


@[path]
private lemma main
  {n : ℕ} [Nonempty (Fin n)]
  {x : Fin n → ℝ}
  {M : Fin n}
-- given
  (h : M = ReducedArgMax x) :
-- imply
  ∀ k : Fin n, (k : ℕ) < (M : ℕ) → x M > x k := by
-- proof
  subst h
  intro k hk
  obtain hlt | heq := lt_or_eq_of_le (ReducedArgMax.le x k)
  · exact hlt
  · have hle : (ReducedArgMax x).val ≤ k.val :=
      Fin.le_def.mp
        (ReducedArgMax.le_of_forall_le x fun j => (ReducedArgMax.le x j).trans (le_of_eq heq.symm))
    omega


-- created on 2026-10-09
