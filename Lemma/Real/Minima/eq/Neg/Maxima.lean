import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ} :
-- imply
  Minima S f = -Maxima S (fun x => -f x) := by
-- proof
  unfold Minima Maxima
  rw [Real.sInf_def]
  congr 2
  ext y
  simp only [Set.mem_neg, Set.mem_image]
  constructor
  · rintro ⟨x, hx, e⟩
    exact ⟨x, hx, by linarith⟩
  · rintro ⟨x, hx, e⟩
    exact ⟨x, hx, by linarith⟩


-- created on 2020-09-30
