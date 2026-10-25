-- Carved from Lemma/Definitions/Def_DedekindDomain_FiniteAdeleRing_BaseChange.lean: instance decls only.
import Instance.DedekindDomain_Completion_BaseChange
import Lemma.DedekindDomain.FiniteAdeleRing_TensorRestrictedProduct
import Instance.Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Notation.DedekindDomain_FiniteAdeleRing_BaseChange
import Class.DedekindDomain_FiniteAdeleRing_BaseChange

set_option maxSynthPendingDepth 3
set_option Elab.async false

namespace ContinuousSemialgHom

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)

instance instFunLike : FunLike (A →SA[φ] B) A B where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective h

instance : CoeOut (A →SA[φ] B) (A →ₛₐ[φ] B) :=
  ⟨fun f => f.toSemialgHom⟩

variable (F : Type*) (A B : outParam Type*)

instance : ContinuousSemialgHomClass (A →SA[φ] B) φ A B where
  map_add ψ := ψ.map_add
  map_smulₛₗ ψ := ψ.map_smulₛₗ
  map_mul ψ := ψ.map_mul
  map_one ψ := ψ.map_one
  map_zero ψ := ψ.map_zero
  continuous_toFun ψ := ψ.continuous_toFun

instance : CoeTC F (A →SA[φ] B) :=
  ⟨ContinuousSemialgHomClass.toContinuousSemialgHom⟩

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

instance : SMul (Πʳ i, [R i, B i]_[ℱ]) (Πʳ i, [M i, C i]_[ℱ]) where
  smul r m := ⟨fun i ↦ (r i) • (m i), by
    filter_upwards [r.prop, m.prop] with i hr hm using SMulMemClass.smul_mem ⟨r i, hr⟩ hm⟩

instance instModuleCoe_fLT : Module (Πʳ i, [R i, B i]_[ℱ]) (Πʳ i, [M i, C i]_[ℱ]) where
  zero_smul m := by ext; simp
  smul_zero r := by ext; simp
  one_smul m := by ext; simp
  add_smul r s m:= by ext; simp [add_smul]
  smul_add r m n := by ext; simp
  mul_smul r s m := by ext; simp [mul_smul]

variable {M₂ : ι → Type*} [Π i, AddCommGroup (M₂ i)] [Π i, Module (R i) (M₂ i)]
variable {N₂ : ι → Type*}
variable [Π i, SetLike (N₂ i) (M₂ i)] [∀ i, AddSubgroupClass (N₂ i) (M₂ i)]
variable [∀ i, SMulMemClass (N₂ i) (B i) (M₂ i)]
variable {C₂ : Π i, N₂ i}


variable [Π i, TopologicalSpace (R i)] [Π i, TopologicalSpace (M i)]

section continuous_smul

variable [∀ i, ContinuousSMul (R i) (M i)] (T : Set ι)

open scoped Filter in
instance : ContinuousSMul (Πʳ i, [R i, B i]_[𝓟 T]) (Πʳ i, [M i, C i]_[𝓟 T]) :=
  isEmbedding_coe_of_principal.continuousSMul isEmbedding_coe_of_principal.continuous
    (fun {c x} ↦ by ext; rfl)

variable [hBopen : Fact (∀ i, IsOpen (B i : Set (R i)))]
variable [hCopen : Fact (∀ i, IsOpen (C i : Set (M i)))]

instance [∀ i, ContinuousSMul (R i) (M i)] :
    ContinuousSMul (Πʳ i, [R i, B i]) (Πʳ i, [M i, C i]) where
  continuous_smul := by
    rw [continuous_dom_prod hBopen.elim hCopen.elim]
    exact fun S hS ↦ (continuous_inclusion hS).comp continuous_smul

end continuous_smul


variable [∀ i, IsTopologicalRing (R i)]
variable [∀ i, IsModuleTopology (R i) (M i)]
variable [Module.Finite (Πʳ i, [R i, B i]) (Πʳ i, [M i, C i])]

end RestrictedProduct
end


section

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]

namespace IsDedekindDomain

open IsDedekindDomain HeightOneSpectrum adicCompletion Extension

open scoped TensorProduct

namespace FiniteAdeleRing

open scoped TensorProduct.RightActions RestrictedProduct

variable [Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]

instance : Algebra (Πʳ v : HeightOneSpectrum A, [v.adicCompletion K, v.adicCompletionIntegers K])
    (Πʳ w: HeightOneSpectrum B, [w.adicCompletion L, w.adicCompletionIntegers L]) :=
  inferInstanceAs (Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L])


variable [ComapFiberwiseSMul A K L B]

noncomputable section bijection

instance [FiniteDimensional K L] : Module.Finite 𝔸ᶠ[A, K] 𝔸ᶠ[B, L] :=
  Module.Finite.equiv (FiniteAdeleRing.baseChangeAdeleAlgEquiv A K L B).toLinearEquiv

end bijection

section moduleTopology


noncomputable local instance (v : HeightOneSpectrum A) : Module (adicCompletionIntegers K v)
    ((w : Extension B v) → adicCompletion L w.val) :=
  Module.compHom _ (algebraMap (adicCompletionIntegers K v) (adicCompletion K v))

noncomputable local instance (v : HeightOneSpectrum A) : SMul (adicCompletionIntegers K v)
    ((w : Extension B v) → adicCompletion L w.val) :=
  Module.toDistribMulAction.toDistribSMul.toSMul

noncomputable local instance (v : HeightOneSpectrum A) : MulAction (v.adicCompletionIntegers K)
    (v.adicCompletion K) := LieAlgebra.ofAssociativeAlgebra.toMulAction


private noncomputable local instance (priority := 9999) (v : HeightOneSpectrum A) :
    Module (adicCompletion K v) ((w : Extension B v) → adicCompletion L w.val) :=
  Algebra.toModule

set_option synthInstance.maxHeartbeats 80000 in

set_option maxHeartbeats 400000 in

noncomputable local instance : Module 𝔸ᶠ[A, K]
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.1,
    ↑(piAdicIntegerSubmodule A K L B v)] :=
  RestrictedProduct.instModuleCoe_fLT


set_option synthInstance.maxHeartbeats 40000 in

set_option maxHeartbeats 400000 in
instance [FiniteDimensional K L] : IsModuleTopology 𝔸ᶠ[A, K] 𝔸ᶠ[B, L] :=
  have := restrictedProduct_pi_isModuleTopology A K L B
  IsModuleTopology.iso (FiniteAdeleRing.restrictedProduct_pi_equiv A K L B)

end moduleTopology

end FiniteAdeleRing
end IsDedekindDomain
end
