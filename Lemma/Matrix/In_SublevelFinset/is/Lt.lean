import Mathlib
import sympy.Basic
import sympy.matrices.inner_product_space.DiscreteSpectrum
open scoped BigOperators


/--
[DiscreteSpectrum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DiscreteSpectrum.lean)
-/
@[path]
private lemma mem_sublevel_finset_iff
-- given
  (S : NonnegativeDiscreteSpectrum)
  (Λ : ℝ)
  (j : ℕ) :
-- imply
  j ∈ S.sublevelFinset Λ ↔ S j < Λ := by
-- proof
  apply NonnegativeDiscreteSpectrum.mem_sublevelFinset S Λ j

-- created on 2026-10-10
-- updated on 2026-10-23
