import sympy.concrete.reduced
import sympy.Basic


@[main]
private lemma main
  [Fintype α]
  [Nonempty α]
-- given
  (G : α → α → ℝ)
  (v : α → ℝ)
  (a : α) :
-- imply
  (G + v).max a = Finset.univ.sup' Finset.univ_nonempty (fun b => G a b + v b) := by
-- proof
  exact rfl


-- created on 2026-10-07
