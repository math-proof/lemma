import Instance.DedekindDomain_Completion_BaseChange
import Lemma.DedekindDomain.FiniteAdeleRing_TensorRestrictedProduct
import Instance.Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Notation.DedekindDomain_FiniteAdeleRing_BaseChange
import Instance.DedekindDomain_FiniteAdeleRing_BaseChange
import Class.DedekindDomain_FiniteAdeleRing_BaseChange
import Structure.DedekindDomain_FiniteAdeleRing_BaseChange

set_option maxSynthPendingDepth 3
set_option Elab.async false


namespace ContinuousSemialgHom

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    [TopologicalSpace A] [TopologicalSpace B]

variable (F : Type*) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] [TopologicalSpace A] [TopologicalSpace B] [ContinuousSemialgHomClass F φ A B]

end ContinuousSemialgHom

section

namespace RestrictedProduct

variable {ι : Type*}
variable {R : ι → Type*} [Π i, Ring (R i)]
variable {S : ι → Type*}
variable [Π i, SetLike (S i) (R i)] [∀ i, SubringClass (S i) (R i)]
variable {B : Π i, S i}
variable {ℱ : Filter ι}

variable {M : ι → Type*} [Π i, AddCommGroup (M i)] [Π i, Module (R i) (M i)]
variable {N : ι → Type*}
variable [Π i, SetLike (N i) (M i)] [∀ i, AddSubgroupClass (N i) (M i)]
variable [∀ i, SMulMemClass (N i) (B i) (M i)]
variable {C : Π i, N i}

section components

variable [DecidableEq ι]

end components

variable [Π i, TopologicalSpace (R i)] [Π i, TopologicalSpace (M i)]

section continuous_smul

variable [∀ i, ContinuousSMul (R i) (M i)] (T : Set ι)

variable [hBopen : Fact (∀ i, IsOpen (B i : Set (R i)))]
variable [hCopen : Fact (∀ i, IsOpen (C i : Set (M i)))]

end continuous_smul

section components

variable [Π i, TopologicalSpace (M₂ i)]

end components

section free_topology

variable (n : Type*)

end free_topology

variable [∀ i, IsTopologicalRing (R i)]
variable [∀ i, IsModuleTopology (R i) (M i)]
variable [Module.Finite (Πʳ i, [R i, B i]) (Πʳ i, [M i, C i])]

end RestrictedProduct
end

section

end

section

namespace IsDedekindDomain.FiniteAdeleRing

variable (R K : Type*) [CommRing R] [Field K] [IsDedekindDomain R] [Algebra R K]
  [IsFractionRing R K]

noncomputable abbrev integralAdeles : Subring (FiniteAdeleRing R K) :=
  RestrictedProduct.structureSubring _ _ _

variable {R K}

abbrev mk (f : ∀ v, HeightOneSpectrum.adicCompletion K v)
    (h : ∀ᶠ (i : HeightOneSpectrum R) in Filter.cofinite,
    f i ∈ (fun v ↦ ↑(HeightOneSpectrum.adicCompletionIntegers K v)) i) : FiniteAdeleRing R K :=
  ⟨f, h⟩
end IsDedekindDomain.FiniteAdeleRing

end

section

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L] [Module.Finite A B]
    [IsDedekindDomain B] [IsFractionRing B L]

namespace IsDedekindDomain

open IsDedekindDomain HeightOneSpectrum adicCompletion Extension

open scoped TensorProduct

namespace FiniteAdeleRing

noncomputable section bijection

end bijection

section moduleTopology

attribute [local instance 9999] Algebra.toModule in

attribute [local instance 9999] Algebra.toModule Algebra.toSMul in

end moduleTopology
