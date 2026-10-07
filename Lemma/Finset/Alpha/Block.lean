import sympy.concrete.continued_fraction
import sympy.sets.sets
import sympy.Basic
import Lemma.List.OfFn_Fun.eq.MapRange
open List Continuant


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
  {y : ℝ}
-- given
  (_h₀ : n > 0)
  (_h : ∀ i, x i > 0)
  (_hy : y > 0) :
-- imply
  alpha (List.ofFn (Fin.snoc (α := fun _ => ℝ) (fun i : Fin n => x i) y)) = alpha ((List.range n).map x ++ [y]) := by
-- proof
  rw [List.ofFn_succ', List.concat_eq_append]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, OfFn_Fun.eq.MapRange]


-- created on 2020-09-19
