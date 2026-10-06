import sympy.sets.sets
import sympy.Basic
import Mathlib.Data.Real.Pointwise
import Lemma.Real.Inf_Square.even_function
import Lemma.Real.Inf_Square.eq.Square.of.Ge_0.Lt


open scoped Pointwise


@[main]
private lemma main
  {m : ℝ}
-- given
  (h : m < 0) :
-- imply
  sInf ((fun x => x ^ 2) '' Set.Ioo m 0) = 0 := by
-- proof
  have hIoo : Set.Ioo m 0 = -(Set.Ioo 0 (-m)) := by
    ext x
    simp only [Set.mem_neg, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  have h2 : (0:ℝ) < -m := by linarith
  rw [hIoo, Real.Inf_Square.even_function, Real.Inf_Square.eq.Square.of.Ge_0.Lt le_rfl h2]
  norm_num


-- created on 2019-12-21
-- updated on 2023-05-04
