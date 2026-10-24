import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CoordinateRingRecovery
open AlgebraicGeometry PrimeSpectrum


/--
[specQuasiCompact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoordinateRingRecovery.lean)
-/
@[path]
lemma specQuasiCompact
  {R : Type*}
  [CommRing R] :
-- imply
  CompactSpace (PrimeSpectrum R) :=
-- proof
  PrimeSpectrum.compactSpace
section ClosedSubspace

/--
[closedSubspace_isClosedEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoordinateRingRecovery.lean)
-/
@[path]
lemma closedSubspace_isClosedEmbedding
  {A : Type*}
  [CommRing A]
  {I : Ideal A} :
-- imply
  Topology.IsClosedEmbedding (PrimeSpectrum.comap (Ideal.Quotient.mk I)) :=
-- proof
  PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
    Ideal.Quotient.mk_surjective

/--
[closedSubspace_range_eq_zeroLocus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoordinateRingRecovery.lean)
-/
@[path]
lemma closedSubspace_range_eq_zeroLocus
  {A : Type*}
  [CommRing A]
  {I : Ideal A} :
-- imply
  Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = PrimeSpectrum.zeroLocus (I : Set A) := by
-- proof
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
  congr 1
  ext x
  simp
end ClosedSubspace
section HilbertBasis

/--
[hilbertBasisTheorem_mv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoordinateRingRecovery.lean)
-/
@[path]
lemma hilbertBasisTheorem_mv
  {k : Type*}
  [CommRing k]
  [IsNoetherianRing k]
  {n : ℕ} :
-- imply
  IsNoetherianRing (MvPolynomial (Fin n) k) :=
-- proof
  MvPolynomial.isNoetherianRing_fin

/--
[hilbertBasisTheorem_field](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoordinateRingRecovery.lean)
-/
@[path]
lemma hilbertBasisTheorem_field
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  IsNoetherianRing (MvPolynomial (Fin n) k) :=
-- proof
  MvPolynomial.isNoetherianRing_fin
end HilbertBasis


-- created on 2026-10-23
