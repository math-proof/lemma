import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.VandermondeTypeConvolutionForSRestrictedWeightedCompositions
open scoped BigOperators
open MathlibExt.Combinatorics.Enumerative


/--
[vandermondeTypeConvolutionForSRestrictedWeightedCompositions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/VandermondeTypeConvolutionForSRestrictedWeightedCompositions.lean)
-/
@[path]
private lemma vandermondeTypeConvolutionForSRestrictedWeightedCompositions_eq
  [CommRing R]
  {S : Finset ℕ}
  {f : ℕ → R}
  {n k j : ℕ}
-- given
  (hj : j ≤ k) :
-- imply
  sRestrictedWeightedCompositionCount S f n k =
    ∑ m ∈ Finset.range (n + 1),
    sRestrictedWeightedCompositionCount S f m j *
    sRestrictedWeightedCompositionCount S f (n - m) (k - j) := by
-- proof
  apply MathlibExt.Combinatorics.Enumerative.vandermondeTypeConvolutionForSRestrictedWeightedCompositions S f n k j hj


-- created on 2026-10-20
