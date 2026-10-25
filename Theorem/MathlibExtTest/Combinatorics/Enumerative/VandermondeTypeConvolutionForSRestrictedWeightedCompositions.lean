/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/VandermondeTypeConvolutionForSRestrictedWeightedCompositions.lean -/


import Def.Combinatorics.Enumerative.VandermondeTypeConvolutionForSRestrictedWeightedCompositions
import Lemma.Finset.Enumerative.VandermondeTypeConvolutionForSRestrictedWeightedCompositions
import Mathlib.Algebra.Ring.Int.Defs


namespace MathlibExt.Combinatorics.Enumerative

open scoped BigOperators

/-- Generic use of the Vandermonde-type convolution. -/
example {R : Type*} [CommRing R] (S : Finset ℕ) (f : ℕ → R) (n k j : ℕ) (hj : j ≤ k) :
    sRestrictedWeightedCompositionCount S f n k =
      ∑ m ∈ Finset.range (n + 1),
        sRestrictedWeightedCompositionCount S f m j *
          sRestrictedWeightedCompositionCount S f (n - m) (k - j) :=
  vandermondeTypeConvolutionForSRestrictedWeightedCompositions S f n k j hj

/-- Boundary case: the empty composition of `0` has weight `1`. -/
example : sRestrictedWeightedCompositionCount (R := ℤ) ∅ (fun _ => 1) 0 0 = 1 := by
  classical
  unfold sRestrictedWeightedCompositionCount
  simp

/-- Boundary case: there is no composition of `1` with `0` parts. -/
example : sRestrictedWeightedCompositionCount (R := ℤ) ∅ (fun _ => 1) 1 0 = 0 := by
  classical
  unfold sRestrictedWeightedCompositionCount
  simp

end MathlibExt.Combinatorics.Enumerative
