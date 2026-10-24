/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Idele.lean -/

/-
Author: @toskua, Avocado
-/

import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Group.Units

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

/-- The integral unit subgroup `O_vˣ` of the multiplicative group of the completion at `v`. -/
abbrev localIntegralUnitSubgroup (v : HeightOneSpectrum R) :
    Subgroup ((v.adicCompletion K)ˣ) :=
  (Submonoid.ofClass (v.adicCompletionIntegers K)).units

@[simp]
theorem mem_localIntegralUnitSubgroup {v : HeightOneSpectrum R} {u : (v.adicCompletion K)ˣ} :
    u ∈ localIntegralUnitSubgroup R K v ↔
      (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
        ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈
          v.adicCompletionIntegers K :=
  Iff.rfl

/-- The finite ideles, with the restricted-product topology. -/
def FiniteIdeleGroup :=
  Πʳ v : HeightOneSpectrum R,
    [(v.adicCompletion K)ˣ, localIntegralUnitSubgroup R K v]

namespace FiniteIdeleGroup

instance : CommGroup (FiniteIdeleGroup R K) := inferInstanceAs <|
  CommGroup <| Πʳ v : HeightOneSpectrum R,
    [(v.adicCompletion K)ˣ, localIntegralUnitSubgroup R K v]

instance : TopologicalSpace (FiniteIdeleGroup R K) := inferInstanceAs <|
  TopologicalSpace <| Πʳ v : HeightOneSpectrum R,
    [(v.adicCompletion K)ˣ, localIntegralUnitSubgroup R K v]

instance : DFunLike (FiniteIdeleGroup R K) (HeightOneSpectrum R)
    (fun v ↦ (v.adicCompletion K)ˣ) where
  coe a := a.1
  coe_injective _ _ := Subtype.ext

/-- The integral unit subgroup at a finite place is open in the local multiplicative group. -/
theorem isOpen_localIntegralUnitSubgroup (v : HeightOneSpectrum R) :
    IsOpen (localIntegralUnitSubgroup R K v : Set ((v.adicCompletion K)ˣ)) := by
  let O := v.adicCompletionIntegers K
  have hO : IsOpen (O : Set (v.adicCompletion K)) := Valued.isOpen_valuationSubring _
  rw [show (localIntegralUnitSubgroup R K v : Set ((v.adicCompletion K)ˣ)) =
      Units.val ⁻¹' (O : Set (v.adicCompletion K)) ∩
        (fun x : (v.adicCompletion K)ˣ ↦
          ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ⁻¹'
            (O : Set (v.adicCompletion K)) by
    ext x
    rfl]
  exact (hO.preimage Units.continuous_val).inter
    (hO.preimage (Units.continuous_val.comp continuous_inv))

instance : IsTopologicalGroup (FiniteIdeleGroup R K) :=
  haveI : Fact (∀ v : HeightOneSpectrum R,
      IsOpen (localIntegralUnitSubgroup R K v : Set ((v.adicCompletion K)ˣ))) :=
    ⟨isOpen_localIntegralUnitSubgroup R K⟩
  RestrictedProduct.isTopologicalGroup
    (fun v : HeightOneSpectrum R ↦ (v.adicCompletion K)ˣ)

end FiniteIdeleGroup

/-- The infinite ideles, with the product topology. -/
def InfiniteIdeleGroup := (v : InfinitePlace K) → (v.Completion)ˣ

namespace InfiniteIdeleGroup

instance : CommGroup (InfiniteIdeleGroup K) := inferInstanceAs <|
  CommGroup <| (v : InfinitePlace K) → (v.Completion)ˣ

instance : TopologicalSpace (InfiniteIdeleGroup K) := inferInstanceAs <|
  TopologicalSpace <| (v : InfinitePlace K) → (v.Completion)ˣ

instance : IsTopologicalGroup (InfiniteIdeleGroup K) := inferInstanceAs <|
  IsTopologicalGroup <| (v : InfinitePlace K) → (v.Completion)ˣ

end InfiniteIdeleGroup

-- Upstream `NumberField.IdeleGroup` (`𝔸[R, K]ˣ`) and
-- `NumberField.IdeleClassGroup` are reused unshadowed. The restricted-product
-- model below uses the explicit `TopologicalIdeleGroup` type to preserve the local
-- topology; see `TopologicalIdeleGroup.unitsEquiv` for the algebraic bridge.

/-- The topological idele group, with the standard product/restricted-product topology.

This is the product of the infinite ideles and the finite ideles. It carries the
product of the infinite-place product topology and the finite restricted-product
topology, which differs from the subspace topology on the units of the adele ring.
Upstream `NumberField.IdeleGroup` (`𝔸[R, K]ˣ`) is a distinct type. -/
def TopologicalIdeleGroup :=
  (InfiniteIdeleGroup K × FiniteIdeleGroup R K)

namespace TopologicalIdeleGroup

instance : CommGroup (TopologicalIdeleGroup R K) := inferInstanceAs <|
  CommGroup (InfiniteIdeleGroup K × FiniteIdeleGroup R K)

instance : TopologicalSpace (TopologicalIdeleGroup R K) := inferInstanceAs <|
  TopologicalSpace (InfiniteIdeleGroup K × FiniteIdeleGroup R K)

instance : IsTopologicalGroup (TopologicalIdeleGroup R K) := inferInstanceAs <|
  IsTopologicalGroup (InfiniteIdeleGroup K × FiniteIdeleGroup R K)

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
/-- The topological idele class group, namely the quotient of the topological idele
group by principal ideles. Upstream `NumberField.IdeleClassGroup` (the quotient of
`𝔸[R, K]ˣ`) is a distinct type. -/
abbrev TopologicalIdeleClassGroup :=
  (TopologicalIdeleGroup R K) ⧸ (TopologicalIdeleGroup.principalIdeles R K)

end NumberField
