import sympy.sets.sets
import sympy.Basic
import Mathlib.Data.Real.Pointwise
import Lemma.Real.Inf_Square.even_function
import Lemma.Real.Inf_Square.eq.Square.of.Ge_0.Lt


open scoped Pointwise


@[path]
private lemma main
  {m M : ℝ}
-- given
  (hM : M ≤ 0)
  (h : m < M) :
-- imply
  sInf ((fun x => x ^ 2) '' Set.Ioo m M) = M ^ 2 := by
-- proof
  have hIoo : Set.Ioo m M = -(Set.Ioo (-M) (-m)) := by
    ext x
    simp only [Set.mem_neg, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  have h1 : -M ≥ 0 := by linarith
  have h2 : -M < -m := by linarith
  rw [hIoo, Real.Inf_Square.even_function, Real.Inf_Square.eq.Square.of.Ge_0.Lt h1 h2]
  ring


-- created on 2019-12-08
-- updated on 2023-05-06
