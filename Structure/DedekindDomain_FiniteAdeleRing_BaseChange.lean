import Instance.DedekindDomain_Completion_BaseChange
import Lemma.DedekindDomain.FiniteAdeleRing_TensorRestrictedProduct
import Instance.Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Notation.DedekindDomain_FiniteAdeleRing_BaseChange
import Instance.DedekindDomain_FiniteAdeleRing_BaseChange
import Class.DedekindDomain_FiniteAdeleRing_BaseChange

set_option maxSynthPendingDepth 3
set_option Elab.async false

/-- A `SemialgHom` (i.e., `ψ` such that `ψ (r • a) = φ r • ψ a` for some `φ : R →+* S`) that
is also continuous. -/
structure ContinuousSemialgHom {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (A B : Type*) [TopologicalSpace A] [TopologicalSpace B]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    extends SemialgHom φ A B where
  continuous_toFun : Continuous toFun

namespace ContinuousSemialgHom

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    [TopologicalSpace A] [TopologicalSpace B]

variable (F : Type*) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] [TopologicalSpace A] [TopologicalSpace B] [ContinuousSemialgHomClass F φ A B]

variable {F} {φ} {A} {B} in


variable {φ A B} in


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

omit [Π i, AddSubgroupClass (N i) (M i)] in


variable {M₂ : ι → Type*} [Π i, AddCommGroup (M₂ i)] [Π i, Module (R i) (M₂ i)]
variable {N₂ : ι → Type*}
variable [Π i, SetLike (N₂ i) (M₂ i)] [∀ i, AddSubgroupClass (N₂ i) (M₂ i)]
variable [∀ i, SMulMemClass (N₂ i) (B i) (M₂ i)]
variable {C₂ : Π i, N₂ i}

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

omit [(i : ι) → TopologicalSpace (R i)] in

end components

section free_topology

variable (n : Type*)

variable (B) in


variable [∀ i, IsTopologicalRing (R i)]


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


variable {R K}


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


set_option backward.isDefEq.respectTransparency false in

variable {A K B} in

open scoped TensorProduct.RightActions RestrictedProduct

variable [Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]


variable [ComapFiberwiseSMul A K L B]

variable {A K L B} in

variable {A K B} in

noncomputable section bijection


set_option synthInstance.maxHeartbeats 40000 in

set_option maxHeartbeats 400000 in


set_option backward.isDefEq.respectTransparency false in
omit [IsFractionRing B L] in

set_option synthInstance.maxHeartbeats 40000 in

set_option maxHeartbeats 400000 in


set_option synthInstance.maxHeartbeats 40000 in

set_option maxHeartbeats 400000 in


set_option synthInstance.maxHeartbeats 40000 in

set_option maxHeartbeats 400000 in


set_option synthInstance.maxHeartbeats 40000 in

set_option maxHeartbeats 400000 in

set_option backward.isDefEq.respectTransparency false in


end bijection

section moduleTopology


set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 80000 in

set_option maxHeartbeats 400000 in


set_option synthInstance.maxHeartbeats 160000 in

set_option maxHeartbeats 800000 in

end moduleTopology
