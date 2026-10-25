/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Idele.lean -/

/-
Author: @toskua, Avocado
-/

import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Group.Units
import Def.NumberTheory.NumberField.Idele.Part4
/-!
# Ideles of a number field

This file defines ideles with their standard topology. The finite ideles are a restricted product
of the groups `K_vˣ` with respect to the integral unit subgroups `O_vˣ`. This is not the topology
that the units of the adele ring inherit as a subspace.

The full idele group is the product of the groups at infinite places and the finite ideles. We also
define the diagonal principal-idèle embedding and the idele class group, and record the algebraic
equivalence with the units of the adele ring.

The canonical number-field specialization uses `R = 𝓞 K`. As with `NumberField.AdeleRing`, the
definitions are stated for a Dedekind domain `R` with fraction field `K`, allowing convenient
specializations such as `R = ℤ` and `K = ℚ`. They do not model global function-field ideles.

## References

* arXiv:2607.28465v3, *Deformation of the absolute Galois groups of number fields*, line 246
* arXiv:2608.04982v1, *Weyl Subconvexity for GL₂ with Simple Supercuspidal Ramification*,
  lines 612--614
* arXiv:2608.23886v1, *Fourier Spectral Reciprocity and Canonical Hecke L-Functions*,
  lines 201--202
-/


noncomputable section

open scoped RestrictedProduct NumberField.AdeleRing

namespace NumberField

open InfinitePlace AbsoluteValue.Completion InfinitePlace.Completion IsDedekindDomain

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The topological idele class group, namely the quotient of the topological idele
group by principal ideles. Upstream `NumberField.IdeleClassGroup` (the quotient of
`𝔸[R, K]ˣ`) is a distinct type. -/
abbrev TopologicalIdeleClassGroup :=
  (TopologicalIdeleGroup R K) ⧸ (TopologicalIdeleGroup.principalIdeles R K)

end NumberField
end
