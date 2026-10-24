import Lemma.Definitions.Def_M4aHerbrand_ModuleTopologyBridge
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

namespace M4aHerbrand.Bridge

open NumberField IsDedekindDomain TensorProduct

section OMT

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [Algebra A B]

theorem isModuleTopology_of_continuous_algebraMap_of_sigmaCompact
    [SigmaCompactSpace A] [T2Space B] [BaireSpace B] [Module.Free A B] [Module.Finite A B]
    (hβ : Continuous (algebraMap A B)) : IsModuleTopology A B := by
  let b := Module.Free.chooseBasis A B
  let Φ : (Module.Free.ChooseBasisIndex A B → A) ≃ₗ[A] B := b.equivFun.symm
  have hΦ : Continuous Φ := by
    have he : (Φ : (Module.Free.ChooseBasisIndex A B → A) → B)
        = fun c => ∑ i, algebraMap A B (c i) * b i := by
      funext c
      show b.equivFun.symm c = _
      rw [b.equivFun_symm_apply]
      simp_rw [Algebra.smul_def]
    rw [he]
    exact continuous_finsetSum _ fun i _ => (hβ.comp (continuous_apply i)).mul continuous_const
  have hopen : IsOpenMap Φ :=
    AddMonoidHom.isOpenMap_of_sigmaCompact Φ.toLinearMap.toAddMonoidHom Φ.surjective hΦ
  have hsymm : Continuous Φ.symm :=
    (Φ.toEquiv.toHomeomorphOfContinuousOpen hΦ hopen).continuous_symm
  let Ψ : (Module.Free.ChooseBasisIndex A B → A) ≃L[A] B :=
    { Φ with continuous_toFun := hΦ, continuous_invFun := hsymm }
  exact IsModuleTopology.iso Ψ

end OMT

section Adele

variable (R E : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E]
  [IsFractionRing R E]
variable (S F : Type*) [CommRing S] [IsDedekindDomain S] [Field F] [Algebra S F]
  [IsFractionRing S F]
variable [Algebra E F]

open scoped RestrictedProduct in

instance instT2SpaceAdeleRing : T2Space (AdeleRing S F) :=
  inferInstanceAs (T2Space (((v : InfinitePlace F) → v.Completion) ×
    Πʳ v : HeightOneSpectrum S, [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem isModuleTopology_adeleRing_of_continuous [Module.Finite E F]
    [Algebra (AdeleRing R E) (AdeleRing S F)]
    [SigmaCompactSpace (AdeleRing R E)] [LocallyCompactSpace (AdeleRing S F)]
    (hβ : Continuous (algebraMap (AdeleRing R E) (AdeleRing S F)))
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F) :
    IsModuleTopology (AdeleRing R E) (AdeleRing S F) := by
  haveI : Module.Free (AdeleRing R E) (AdeleRing S F) := Module.Free.of_equiv te.toLinearEquiv
  haveI : Module.Finite (AdeleRing R E) (AdeleRing S F) := Module.Finite.equiv te.toLinearEquiv
  exact isModuleTopology_of_continuous_algebraMap_of_sigmaCompact hβ

theorem continuous_conjAct_of_continuous [Module.Finite E F]
    [Algebra (AdeleRing R E) (AdeleRing S F)]
    [SigmaCompactSpace (AdeleRing R E)] [LocallyCompactSpace (AdeleRing S F)]
    (hβ : Continuous (algebraMap (AdeleRing R E) (AdeleRing S F)))
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F) (σ : F ≃ₐ[E] F) :
    Continuous (conjAct R E S F te σ) :=
  haveI := isModuleTopology_adeleRing_of_continuous R E S F hβ te
  continuous_conjAct R E S F te σ

end Adele

end M4aHerbrand.Bridge
