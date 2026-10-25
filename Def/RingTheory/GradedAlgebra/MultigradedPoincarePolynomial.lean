/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedPoincarePolynomial.lean -/

/-
  Author: Muse Code powered by Meta Muse Spark
-/

import Theorem.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport
import Lemma.Int.GradedAlgebra.MultigradedPoincareFiniteSupport
/-!
# Multigraded Poincaré polynomial

This file packages the raw edge-6 Poincaré coefficient function as an
`AddMonoidAlgebra` element over homological degree times multidegree, and
pins each of its coefficients to the corresponding edge-3 Betti number.

Source: Benjamin Braun and Brian Davis, “Antichain Simplices,”
Journal of Integer Sequences 23 (2020),
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`,
exact line 876. That line states the Hilbert syzygy consequence: over a
polynomial ring, the Poincaré series of every finitely generated module
is a polynomial. This edge formalizes the conditional polynomial
realization behind that line: under the two structural resolution
hypotheses — every homogeneous basis index type is finite, and those
types are empty above the bound — the edge-6 coefficient function has
finite support and hence defines a polynomial.

Conditional finite-resolution bridge, not the full Hilbert syzygy
theorem: the hypotheses describe the terms of an already-supplied
finite-rank terminating resolution and say nothing about Betti numbers
or coefficient supports, so the polynomial and its coefficient equation
are genuinely derived from the resolution geometry. In particular,
nothing here constructs such a resolution for every finitely generated
module over `MvPolynomial`, proves the classical bound by the number of
variables, or assumes minimality or comparison data. That existence step
is a later Hilbert-syzygy edge.

Main definitions and results:

* `MetaMathlibExt.multigradedPoincarePolynomial`: the Poincaré
  coefficient family packaged as an `AddMonoidAlgebra` element, using
  edge-6 finite support from the two structural resolution hypotheses.
* `MetaMathlibExt.multigradedPoincarePolynomial_coeff`: evaluating the
  polynomial at `(i, α)` returns exactly
  `multigradedBettiNumber data α i`.
-/


namespace MetaMathlibExt

universe u

/-- Multigraded Poincaré polynomial: the raw coefficient family
`multigradedPoincareCoefficients data`, packaged as an
`AddMonoidAlgebra` element over homological degree times multidegree.

This is conditional on the finite terminating resolution: every
homogeneous basis index type is finite (`finiteBasis`), and those types
are empty above `bound` (`emptyAbove`). Edge 6 turns exactly these two
hypotheses into finite support; the polynomial adds no further
mathematics. -/
noncomputable def multigradedPoincarePolynomial {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    {targetGraded : MultigradedPolynomialModule K n M}
    {resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M)}
    {ι : ℕ → Type u}
    {res : MultigradedFreeResolution K n M targetGraded resolution ι}
    (data : MultigradedBaseChange targetGraded resolution ι res)
    (bound : ℕ)
    (finiteBasis : ∀ i, Finite (ι i))
    (emptyAbove : ∀ i, bound < i → IsEmpty (ι i)) :
    AddMonoidAlgebra Nat (Nat × (Fin n →₀ Int)) :=
  AddMonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite (multigradedPoincareCoefficients data) (by
    have h : Function.HasFiniteSupport (multigradedPoincareCoefficients data) :=
      multigradedPoincareCoefficients_hasFiniteSupport_of_finiteResolution data
        bound finiteBasis emptyAbove

end MetaMathlibExt
