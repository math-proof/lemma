import sympy.core.function
import sympy.Basic


@[path]
private lemma main
  {n d : ℕ}
  {f : ℕ → ℝ → ℝ} :
-- imply
  Difference (fun x => ∑ i ∈ Finset.range n, f i x) d = fun x => ∑ i ∈ Finset.range n, Difference (f i) d x := by
-- proof
  induction d with
  | zero =>
    rfl
  | succ d ih =>
    funext x
    simp only [Difference, Function.iterate_succ_apply'] at ih ⊢
    rw [ih]
    simp [fwdDiff, Finset.sum_sub_distrib]


-- created on 2020-10-11
