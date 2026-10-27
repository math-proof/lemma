import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial Set


namespace Weierstrass

/--
[weierstrass_approximation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/Weierstrass.lean)
-/
@[path]
lemma weierstrass_approximation
  {f : ℝ → ℝ}
  {ε : ℝ}
-- given
  (hf : ContinuousOn f (Icc 0 1))
  (hε : 0 < ε) :
-- imply
  ∃ p : ℝ[X], ∀ x ∈ Icc (0 : ℝ) 1, := by
-- proof
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 f hf ε hε
  exact ⟨p, fun x hx => le_of_lt (hp x hx)⟩

end Weierstrass


-- created on 2026-10-23
