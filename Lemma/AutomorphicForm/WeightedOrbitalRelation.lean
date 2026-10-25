import Lemma.AutomorphicForm.TwistedOrbital
import Def.NumberField_AdelicHeight
import Def.AutomorphicForm_WeightedOrbitalRelation

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField IsDedekindDomain TopologicalSpace TensorProduct
open scoped TensorProduct.RightActions

namespace AutomorphicForm

namespace LocalWeight

variable {F : Type*} [NormedField F]


theorem weight_one : weight (1 : GL (Fin 2) F) = 0 := by
  simp [weight, AdelicHeight.rowMaxNorm]

end LocalWeight

section Untwisted

variable (A : Type) [CommRing A] [TopologicalSpace A]


theorem isWeightedOrbitalIntegralOn_zero (μ : @Measure (GL (Fin 2) A) (glBorelOf A)) (wt : GL (Fin 2) A → ℝ)
    (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ)) :
    IsWeightedOrbitalIntegralOn A μ wt γ τ (fun _ => 0) 0 :=
  ⟨fun _ => 0, isSectionFnOn_zero A γ τ, by simp⟩

end Untwisted

section Twisted

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] (σ : L ≃ₐ[K] L)


theorem isTwistedWeightedOrbitalIntegralOn_zero
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A))) (wt : GL (Fin 2) (L ⊗[K] A) → ℝ)
    (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)) :
    IsTwistedWeightedOrbitalIntegralOn K L A σ μ wt δ τ' (fun _ => 0) 0 :=
  ⟨fun _ => 0, isTwistedSectionFnOn_zero K L A σ δ τ', by simp⟩

end Twisted

section FinitePlaces

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)


theorem isWeightedOrbitalIntegral_zero (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ)) :
    IsWeightedOrbitalIntegral K v γ τ (fun _ => 0) 0 :=
  isWeightedOrbitalIntegralOn_zero _ _ _ γ τ

theorem isTwistedWeightedOrbitalIntegral_zero (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ)) :
    IsTwistedWeightedOrbitalIntegral K L v σ δ τ' (fun _ => 0) 0 :=
  isTwistedWeightedOrbitalIntegralOn_zero K L _ σ _ _ δ τ'

end FinitePlaces

end AutomorphicForm

end
