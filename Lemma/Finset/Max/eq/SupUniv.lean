import sympy.concrete.reduced
import sympy.Basic


@[main]
private lemma main
  [Fintype α]
  [Nonempty α]
-- given
  (v : α → ℝ) :
-- imply
  v.max = Finset.univ.sup' Finset.univ_nonempty v := by
-- proof
  exact rfl


-- created on 2026-10-07
