import Mathlib.Analysis.Normed.Field.Krasner
/-!
# Closest conjugates and Krasner's lemma

This file defines when an algebraic element is closer to one element than to all of its
other conjugates, and connects this condition to Krasner's lemma.
-/


namespace AlgebraicClosure

/-- `α` is the closest conjugate to `β` if `β` is closer to `α` than to every image of
`α` under a nontrivial `K`-algebra automorphism of the algebraic closure. -/
def IsClosestConjugate (K : Type*) [NormedField K]
    (α β : AlgebraicClosure K) : Prop :=
  ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
    σ α ≠ α →
    spectralNorm K (AlgebraicClosure K) (β - α) <
      spectralNorm K (AlgebraicClosure K) (β - σ α)

end AlgebraicClosure
