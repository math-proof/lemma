import sympy.sets.sets
import sympy.Basic
import Lemma.Real.Inf.eq.Neg.Sup


open scoped Pointwise


@[path]
private lemma main
  {f : ℝ → ℝ}
  {S : Set ℝ}
-- given
  (h : ∀ x, f (-x) = -f x) :
-- imply
  sInf (f '' (-S)) = -sSup (f '' S) := by
-- proof
  rw [Real.Inf.eq.Neg.Sup]
  have himg : (fun x => -f x) '' (-S) = f '' S := by
    ext z
    constructor
    ·
      rintro ⟨x, hx, rfl⟩
      exact ⟨-x, Set.mem_neg.mp hx, h x⟩
    ·
      rintro ⟨x, hx, rfl⟩
      exact ⟨-x, by simp [hx], by simp [h]⟩
  rw [himg]


-- created on 2019-09-18
-- updated on 2022-09-20
