/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedPoincareFiniteSupport.lean -/

/-
  Author: Muse Code powered by Meta Muse Spark
-/

import Def.RingTheory.GradedAlgebra.MultigradedPoincareCoefficients
import Lemma.Int.GradedAlgebra.MultigradedPoincareCoefficients
/-!
# Finite support of multigraded Poincaré coefficients

This file proves that the raw edge-6 Poincaré coefficient function has
finite support once the underlying multigraded free resolution has finite
homogeneous bases in each homological degree and terminates above a
supplied homological bound.

Source: Benjamin Braun and Brian Davis, “Antichain Simplices,”
Journal of Integer Sequences 23 (2020),
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`,
exact line 876. That line states the Hilbert syzygy consequence: over a
polynomial ring, the Poincaré series of every finitely generated module
is a polynomial. For the edge-6 raw coefficient function, polynomiality
is exactly finite support on homological degree times multidegree.

Conditional finite-resolution bridge, not the full Hilbert syzygy
theorem: the two hypotheses describe the terms of an already-supplied
finite-rank terminating resolution — every homogeneous basis index type
is finite, and those types are empty above the bound. The hypotheses say
nothing about supports, Betti numbers, or Poincaré coefficients, so
finite support is genuinely derived from the resolution geometry:
outside the finite set of actual homogeneous basis degrees, the degree
piece is the span of the empty set, the component complex is zero there,
and the Betti coefficient vanishes. In particular, nothing here
constructs such a resolution for every finitely generated module over
`MvPolynomial`, proves the classical bound by the number of variables,
or assumes finite coefficient support, eventual Betti vanishing, a
`Finsupp` or `AddMonoidAlgebra` value, minimality, or comparison data.
That existence step is a later Hilbert-syzygy edge.

Main results:

* `MetaMathlibExt.multigradedPoincareCoefficients_hasFiniteSupport_of_finiteResolution`:
  the raw coefficient function has finite support under the two
  structural resolution hypotheses above.
-/


namespace MetaMathlibExt

universe u

/-- Recorded homogeneous degree of a term basis index. The
`MultigradedFreeModule` instance on each resolution term is the local
`Module.compHom` instance via `MvPolynomial.C`, so it is installed inside
the body; callers never supply instances. -/
noncomputable def termDeg {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    {targetGraded : MultigradedPolynomialModule K n M}
    {resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M)}
    {ι : ℕ → Type u}
    (res : MultigradedFreeResolution K n M targetGraded resolution ι)
    (i : ℕ) (j : ι i) : Fin n →₀ Int :=
  letI : Module K ↥(resolution.complex.X i) :=
    Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
  (res.termFree i).degree j

end MetaMathlibExt
