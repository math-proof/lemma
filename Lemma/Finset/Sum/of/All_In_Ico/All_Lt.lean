import sympy.concrete.reduced
import sympy.Basic


/--
py `Finset.Sum.of.All_In_Ico.All_Lt`:
masked sum \(\sum_{d_j < i} f(i,j)\) equals the trailing slice from
\(\operatorname{ReducedArgMax}(d - i - n\cdot\mathbf{1}_{d\ge i})\).
-/
@[path]
private lemma main
  {n m : ℕ} [NeZero m]
  {d : Fin m → ℤ}
  {f : ℕ → Fin m → ℝ}
  {i : ℕ}
-- given
  (h_lt : ∀ (i j : Fin m), j < i → d j < d i)
  (h_subset : ∀ j : Fin m, d j ∈ Set.Ico (0 : ℤ) (n : ℤ)) :
-- imply
  let v := fun k : Fin m =>
    (d k : ℝ) - (i : ℝ) - (n : ℝ) * (if (d k : ℤ) ≥ (i : ℤ) then (1 : ℝ) else 0)
  (∑ j ∈ Finset.univ.filter (fun j : Fin m => d j < (i : ℤ)), f i j) =
    ∑ j ∈ Finset.univ.filter (fun j : Fin m => (ReducedArgMax v).val ≤ j.val), f i j := by
-- proof
  sorry


-- created on 2026-10-11
