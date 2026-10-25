import Lemma.AutomorphicForm.TwistedOrbital
import Def.M4aHerbrand_GenuineBeta
import Instance.NumberField_AdelicHaar
import Def.M4aHerbrand_IdeleClassVocab

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped ENNReal TensorProduct

namespace AutomorphicForm.AdelicTracePushforward

section

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable def traceFibre (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (r : AdeleRing (𝓞 K) K) (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K) :
    AdeleRing (𝓞 L) L :=
  M4aHerbrand.Bridge.genuineβ K L r * algebraMap L (AdeleRing (𝓞 L) L) (Module.finrank K L : L)⁻¹ +
    ∑ i, M4aHerbrand.Bridge.genuineβ K L (w i) *
      algebraMap L (AdeleRing (𝓞 L) L) (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i : L)

noncomputable def tracePushforward (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (F : AdeleRing (𝓞 L) L → ℂ) (r : AdeleRing (𝓞 K) K) : ℂ :=
  ∫ w, F (traceFibre K L r w) ∂(Measure.pi fun _ => adelicAddHaar (𝓞 K) K)

noncomputable def actSubId (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L) : AdeleRing (𝓞 L) L :=
  D.act σ x - x

noncomputable def localTraceFibre (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (r : v.adicCompletion K)
    (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → v.adicCompletion K) :
    L ⊗[K] v.adicCompletion K :=
  (Module.finrank K L : L)⁻¹ ⊗ₜ[K] r + ∑ i, (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i : L) ⊗ₜ[K] w i

noncomputable def localTracePushforward (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (f : L ⊗[K] v.adicCompletion K → ℂ) (r : v.adicCompletion K) : ℂ :=
  ∫ w, f (localTraceFibre K L v r w)
    ∂(Measure.pi fun _ =>
      ((Measure.addHaar : Measure (v.adicCompletion K)) (v.adicCompletionIntegers K : Set (v.adicCompletion K)))⁻¹ •
        (Measure.addHaar : Measure (v.adicCompletion K)))

def semiLocalIntegralOutside (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (SK : Finset (HeightOneSpectrum (𝓞 K))) : Set (AdeleRing (𝓞 L) L) :=
  {x | ∀ v ∉ SK, AutomorphicForm.semiLocalEval K L v x.2 ∈ AutomorphicForm.semiLocalIntegers K L v}

def IsSemiLocallyFactorizable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (F : AdeleRing (𝓞 L) L → ℂ) (SK : Finset (HeightOneSpectrum (𝓞 K))) (gL : (w : InfinitePlace L) → w.Completion → ℂ)
    (Fv : (v : HeightOneSpectrum (𝓞 K)) → L ⊗[K] v.adicCompletion K → ℂ) : Prop :=
  ∀ x, F x = (semiLocalIntegralOutside K L SK).indicator
    (fun x => (∏ w, gL w (x.1 w)) * ∏ v ∈ SK, Fv v (AutomorphicForm.semiLocalEval K L v x.2)) x

end

end AutomorphicForm.AdelicTracePushforward
