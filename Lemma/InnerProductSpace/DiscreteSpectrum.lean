import Mathlib
import sympy.Basic
import sympy.matrices.inner_product_space.DiscreteSpectrum

/--
[DiscreteSpectrum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DiscreteSpectrum.lean)
-/
@[path]
private lemma ext_eq
-- given
  {S T : NonnegativeDiscreteSpectrum}
  (h : ∀ j, S j = T j) :
-- imply
  S = T := by
-- proof
  apply NonnegativeDiscreteSpectrum.ext h


/--
[DiscreteSpectrum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DiscreteSpectrum.lean)
-/
@[path]
private lemma sublevel_set_finite_is
-- given
  (S : NonnegativeDiscreteSpectrum)
  (Λ : ℝ) :
-- imply
  (S.sublevelSet Λ).Finite := by
-- proof
  apply NonnegativeDiscreteSpectrum.sublevelSet_finite S Λ


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


/--
[DiscreteSpectrum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DiscreteSpectrum.lean)
-/
@[path]
private lemma riesz_mean_zero_eq
-- given
  (S : NonnegativeDiscreteSpectrum)
  (Λ : ℝ) :
-- imply
  S.rieszMean 0 Λ = S.countingFunction Λ := by
-- proof
  apply NonnegativeDiscreteSpectrum.rieszMean_zero S Λ


-- created on 2026-10-10
