import Lemma.AutomorphicForm.TwistedOrbital
import Def.NumberField_AdelicHeight

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField IsDedekindDomain TopologicalSpace TensorProduct
open scoped TensorProduct.RightActions

namespace AutomorphicForm

namespace LocalWeight

variable {F : Type*} [NormedField F]

def weight (x : GL (Fin 2) F) : ℝ :=
  2 * Real.log
    (max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ *
        AdelicHeight.rowMaxNorm (x : Matrix (Fin 2) (Fin 2) F) /
      ‖(x : Matrix (Fin 2) (Fin 2) F).det‖)

end LocalWeight

section Untwisted

variable (A : Type) [CommRing A] [TopologicalSpace A]

def IsWeightedOrbitalIntegralOn (μ : @Measure (GL (Fin 2) A) (glBorelOf A)) (wt : GL (Fin 2) A → ℝ)
    (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (f : GL (Fin 2) A → ℂ) (J : ℂ) : Prop :=
  letI := glBorelOf A
  ∃ s : GL (Fin 2) A → ℝ, IsSectionFnOn A γ τ f s ∧
    J = ∫ x, f (x⁻¹ * γ * x) * (wt x : ℂ) * (s x : ℂ) ∂μ

end Untwisted

section Twisted

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] (σ : L ≃ₐ[K] L)

def IsTwistedWeightedOrbitalIntegralOn (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (wt : GL (Fin 2) (L ⊗[K] A) → ℝ) (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (J' : ℂ) : Prop :=
  letI := glBorelOf (L ⊗[K] A)
  ∃ s : GL (Fin 2) (L ⊗[K] A) → ℝ, IsTwistedSectionFnOn K L A σ δ τ' φ s ∧
    J' = ∫ x, φ (x⁻¹ * δ * sigmaGL K L A σ x) * (wt x : ℂ) * (s x : ℂ) ∂μ

end Twisted

section FinitePlaces

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

def semiLocalPlaceComponent (w : v.Extension (𝓞 L)) :
    GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L) :=
  Matrix.GeneralLinearGroup.map
    ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
      (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).toAlgEquiv.toRingEquiv.toRingHom)

def semiLocalWeight (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : ℝ :=
  ∑ᶠ w : v.Extension (𝓞 L), LocalWeight.weight (semiLocalPlaceComponent K L v w x)

def IsWeightedOrbitalIntegral (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (J : ℂ) : Prop :=
  IsWeightedOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) LocalWeight.weight γ τ fv J

def IsTwistedWeightedOrbitalIntegral (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (J' : ℂ) : Prop :=
  IsTwistedWeightedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) (semiLocalWeight K L v)
    δ τ' φv J'

end FinitePlaces

end AutomorphicForm

end
