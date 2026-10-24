import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace M4aHerbrand.Bridge

open NumberField IsDedekindDomain TensorProduct

section Transfer

variable {R S A : Type*} [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace A] [Add A]

theorem IsModuleTopology.of_continuousSMul_iff [SMul R A] [SMul S A]
    (h : ∀ t : TopologicalSpace A, @ContinuousSMul R A _ _ t ↔ @ContinuousSMul S A _ _ t)
    [hR : IsModuleTopology R A] : IsModuleTopology S A := by
  refine ⟨?_⟩
  rw [eq_moduleTopology R A]
  show sInf _ = sInf _
  congr 1
  ext t
  simp only [Set.mem_setOf_eq]
  exact and_congr_left' (h t)

theorem IsModuleTopology.of_smul_eq (i₁ i₂ : SMul R A)
    (h : ∀ (r : R) (a : A), i₁.smul r a = i₂.smul r a)
    (h₁ : @IsModuleTopology R _ A _ i₁ _) : @IsModuleTopology R _ A _ i₂ _ := by
  have : i₁ = i₂ := by
    cases i₁; cases i₂; congr; funext r a; exact h r a
  subst this
  exact h₁

end Transfer

section PullBack

variable {R₁ R₂ A : Type*} [TopologicalSpace R₁] [TopologicalSpace R₂]

@[reducible] def smulFst [SMul R₁ A] : SMul (R₁ × R₂) A := ⟨fun p a => p.1 • a⟩

@[reducible] def smulSnd [SMul R₂ A] : SMul (R₁ × R₂) A := ⟨fun p a => p.2 • a⟩

theorem continuousSMul_smulFst_iff [SMul R₁ A] [Zero R₂] (t : TopologicalSpace A) :
    @ContinuousSMul (R₁ × R₂) A smulFst _ t ↔ @ContinuousSMul R₁ A _ _ t := by
  letI : TopologicalSpace A := t
  letI : SMul (R₁ × R₂) A := smulFst
  constructor
  · intro h
    have hc : Continuous fun p : (R₁ × R₂) × A => p.1 • p.2 := h.continuous_smul
    have he : (fun p : R₁ × A => p.1 • p.2)
        = (fun p : (R₁ × R₂) × A => p.1 • p.2) ∘ fun p : R₁ × A => ((p.1, (0 : R₂)), p.2) := by
      funext p; rfl
    exact ⟨by rw [he]; exact hc.comp (by fun_prop)⟩
  · intro h
    have hc : Continuous fun p : R₁ × A => p.1 • p.2 := h.continuous_smul
    have he : (fun p : (R₁ × R₂) × A => p.1 • p.2)
        = (fun p : R₁ × A => p.1 • p.2) ∘ fun p : (R₁ × R₂) × A => (p.1.1, p.2) := by
      funext p; rfl
    exact ⟨by rw [he]; exact hc.comp (by fun_prop)⟩

theorem continuousSMul_smulSnd_iff [SMul R₂ A] [Zero R₁] (t : TopologicalSpace A) :
    @ContinuousSMul (R₁ × R₂) A smulSnd _ t ↔ @ContinuousSMul R₂ A _ _ t := by
  letI : TopologicalSpace A := t
  letI : SMul (R₁ × R₂) A := smulSnd
  constructor
  · intro h
    have hc : Continuous fun p : (R₁ × R₂) × A => p.1 • p.2 := h.continuous_smul
    have he : (fun p : R₂ × A => p.1 • p.2)
        = (fun p : (R₁ × R₂) × A => p.1 • p.2) ∘ fun p : R₂ × A => (((0 : R₁), p.1), p.2) := by
      funext p; rfl
    exact ⟨by rw [he]; exact hc.comp (by fun_prop)⟩
  · intro h
    have hc : Continuous fun p : R₂ × A => p.1 • p.2 := h.continuous_smul
    have he : (fun p : (R₁ × R₂) × A => p.1 • p.2)
        = (fun p : R₂ × A => p.1 • p.2) ∘ fun p : (R₁ × R₂) × A => (p.1.2, p.2) := by
      funext p; rfl
    exact ⟨by rw [he]; exact hc.comp (by fun_prop)⟩

theorem isModuleTopology_smulFst [Add A] [SMul R₁ A] [Zero R₂] [TopologicalSpace A]
    [IsModuleTopology R₁ A] :
    @IsModuleTopology (R₁ × R₂) _ A _ smulFst _ :=
  @IsModuleTopology.of_continuousSMul_iff R₁ (R₁ × R₂) A _ _ _ _ _ smulFst
    (fun t => (continuousSMul_smulFst_iff t).symm) _

theorem isModuleTopology_smulSnd [Add A] [SMul R₂ A] [Zero R₁] [TopologicalSpace A]
    [IsModuleTopology R₂ A] :
    @IsModuleTopology (R₁ × R₂) _ A _ smulSnd _ :=
  @IsModuleTopology.of_continuousSMul_iff R₂ (R₁ × R₂) A _ _ _ _ _ smulSnd
    (fun t => (continuousSMul_smulSnd_iff t).symm) _

end PullBack

section AlgEquiv

variable {R A : Type*} [CommSemiring R] [TopologicalSpace R] [Semiring A] [Algebra R A]
  [TopologicalSpace A] [IsModuleTopology R A] [ContinuousAdd A]

theorem continuous_algEquiv (e : A ≃ₐ[R] A) : Continuous e :=
  (IsModuleTopology.continuous_of_linearMap e.toLinearMap).congr fun _ => rfl

end AlgEquiv

section Adele

variable (R E : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E]
  [IsFractionRing R E]
variable (S F : Type*) [CommRing S] [IsDedekindDomain S] [Field F] [Algebra S F]
  [IsFractionRing S F]
variable [Algebra E F]

noncomputable def conjAct [Algebra (AdeleRing R E) (AdeleRing S F)]
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F)
    (σ : F ≃ₐ[E] F) : AdeleRing S F ≃+* AdeleRing S F :=
  (te.symm.trans ((Algebra.TensorProduct.congr AlgEquiv.refl σ).trans te)).toRingEquiv

theorem continuous_conjAct [Algebra (AdeleRing R E) (AdeleRing S F)]
    [IsModuleTopology (AdeleRing R E) (AdeleRing S F)]
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F) (σ : F ≃ₐ[E] F) :
    Continuous (conjAct R E S F te σ) :=
  (continuous_algEquiv (te.symm.trans ((Algebra.TensorProduct.congr AlgEquiv.refl σ).trans te))).congr
    fun _ => rfl

omit [Algebra E F] in

theorem isModuleTopology_adeleRing_prodMap
    (βi : InfiniteAdeleRing E →+* InfiniteAdeleRing F)
    (βf : FiniteAdeleRing R E →+* FiniteAdeleRing S F)
    (hi : letI := βi.toAlgebra; IsModuleTopology (InfiniteAdeleRing E) (InfiniteAdeleRing F))
    (hf : letI := βf.toAlgebra; IsModuleTopology (FiniteAdeleRing R E) (FiniteAdeleRing S F)) :
    letI : Algebra (AdeleRing R E) (AdeleRing S F) := (RingHom.prodMap βi βf).toAlgebra
    IsModuleTopology (AdeleRing R E) (AdeleRing S F) := by
  letI : Algebra (InfiniteAdeleRing E) (InfiniteAdeleRing F) := βi.toAlgebra
  letI : Algebra (FiniteAdeleRing R E) (FiniteAdeleRing S F) := βf.toAlgebra

  letI mi : Module (InfiniteAdeleRing E × FiniteAdeleRing R E) (InfiniteAdeleRing F) :=
    Module.compHom _ (RingHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing R E))
  letI mf : Module (InfiniteAdeleRing E × FiniteAdeleRing R E) (FiniteAdeleRing S F) :=
    Module.compHom _ (RingHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing R E))
  have hi' : IsModuleTopology (InfiniteAdeleRing E × FiniteAdeleRing R E) (InfiniteAdeleRing F) :=
    IsModuleTopology.of_smul_eq smulFst _ (fun _ _ => rfl) isModuleTopology_smulFst
  have hf' : IsModuleTopology (InfiniteAdeleRing E × FiniteAdeleRing R E) (FiniteAdeleRing S F) :=
    IsModuleTopology.of_smul_eq smulSnd _ (fun _ _ => rfl) isModuleTopology_smulSnd
  have hprod : IsModuleTopology (InfiniteAdeleRing E × FiniteAdeleRing R E)
      (InfiniteAdeleRing F × FiniteAdeleRing S F) := IsModuleTopology.instProd
  exact IsModuleTopology.of_smul_eq _ _ (fun _ _ => rfl) hprod

end Adele

end M4aHerbrand.Bridge
