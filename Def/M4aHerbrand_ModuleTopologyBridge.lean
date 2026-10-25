import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace M4aHerbrand.Bridge

open NumberField IsDedekindDomain TensorProduct


section PullBack

variable {R₁ R₂ A : Type*} [TopologicalSpace R₁] [TopologicalSpace R₂]

@[reducible] def smulFst [SMul R₁ A] : SMul (R₁ × R₂) A := ⟨fun p a => p.1 • a⟩

@[reducible] def smulSnd [SMul R₂ A] : SMul (R₁ × R₂) A := ⟨fun p a => p.2 • a⟩

end PullBack


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

end Adele

end M4aHerbrand.Bridge
