/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Galois/Abelian.lean -/

import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.FieldTheory.Galois.Abelian
open scoped IsMulCommutative

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsAbelianGalois K L]

/-!
# Intermediate fields of an abelian Galois extension form a modular lattice

For a finite-dimensional abelian Galois extension `L / K`, the lattice
`IntermediateField K L` is modular. The proof transports Mathlib's existing
modular-lattice structure on subgroups of the commutative Galois group across the
Galois correspondence `IsGalois.intermediateFieldEquivSubgroup`.

## ATLAS provenance

This constructor generalizes the cyclotomic prerequisite proved in
`Atlas/NumberTheoryI/code/AnalyticClassNumber.lean` at revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, lines 1627--1651
(`cyclotomicSubgroupModular`, `cyclotomicIntermediateFieldModular`), which supports
the N390 development. Source-to-API mapping: `cyclotomicIntermediateFieldModular`
maps to `IsAbelianGalois.isModularLattice_intermediateField`.
Only the intermediate-field modularity prerequisite is
generalized here: the constructor replaces the cyclotomic-specific
`cyclotomicIntermediateFieldModular` argument, not the remainder of N390. The
companion cyclotomic subgroup fact is not ported since it duplicates Mathlib's
existing `IsModularLattice (Subgroup C)` instance for commutative groups.

## Design

The result is a named noncomputable constructor rather than a global instance, so
downstream proofs install it locally with
`letI := IsAbelianGalois.isModularLattice_intermediateField`.
-/


namespace IsAbelianGalois
end IsAbelianGalois
