/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Idele.lean -/

/-
Author: @toskua, Avocado
-/

import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Group.Units
import Instance.NumberTheory.NumberField.Idele.Part4
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

namespace TopologicalIdeleGroup

/-- The diagonal embedding of global units into the infinite ideles. -/
def infinitePrincipalEmbedding : Kˣ →* InfiniteIdeleGroup K :=
  MulEquiv.piUnits.toMonoidHom.comp <|
    Units.map (algebraMap K (InfiniteAdeleRing K)).toMonoidHom

/-- The diagonal embedding of global units into the finite ideles. -/
def finitePrincipalEmbedding : Kˣ →* FiniteIdeleGroup R K :=
  (RestrictedProduct.unitsEquiv
    (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)).toMonoidHom.comp <|
      FiniteAdeleRing.unitEmbedding R K

/-- The diagonal embedding of global units as principal ideles. -/
def principalEmbedding : Kˣ →* TopologicalIdeleGroup R K :=
  (infinitePrincipalEmbedding K).prod (finitePrincipalEmbedding R K)

/-- The subgroup of principal ideles, namely the image of the diagonal embedding. -/
def principalIdeles : Subgroup (TopologicalIdeleGroup R K) :=
  (principalEmbedding R K).range

/-- The algebraic equivalence between units of the adele ring and the topological
idele group.

This is deliberately not a homeomorphism: the topological idele group has the
restricted-product topology, not the topology induced on the units of the adele ring. -/
def unitsEquiv :
    (AdeleRing R K)ˣ ≃* TopologicalIdeleGroup R K :=
  MulEquiv.prodUnits.trans <| MulEquiv.prodCongr MulEquiv.piUnits <|
    RestrictedProduct.unitsEquiv (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)

end TopologicalIdeleGroup
end NumberField
end
