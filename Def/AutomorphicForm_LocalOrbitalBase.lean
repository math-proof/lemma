import Mathlib
import Lemma.Matrix.FactorizableTestFn
import Abbrev.AutomorphicForm_LocalOrbitalBase

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

noncomputable section

namespace AutomorphicForm

section IntegralUnits

variable {A : Type*}

def integralMatrixSet (U : Set A) : Set (Matrix (Fin 2) (Fin 2) A) := {m | ∀ i j, m i j ∈ U}

variable [CommRing A]

def integralUnitsSet (U : Set A) : Set (GL (Fin 2) A) :=
  {g | (g : Matrix (Fin 2) (Fin 2) A) ∈ integralMatrixSet U ∧
    ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) ∈ integralMatrixSet U}

end IntegralUnits

section Local

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

def IsLocalTestFn (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) : Prop :=
  IsLocallyConstant fv ∧ HasCompactSupport fv

def localAt : GL (Fin 2) (AdeleRing (𝓞 K) K) →* GL (Fin 2) (v.adicCompletion K) :=
  (AdelicLevel.finComponent (𝓞 K) K v).comp (AdelicLevel.glFin (𝓞 K) K)

def localIntegralSet : Set (GL (Fin 2) (v.adicCompletion K)) :=
  integralUnitsSet (v.adicCompletionIntegers K : Set (v.adicCompletion K))

def localIntegralCompacts : PositiveCompacts (GL (Fin 2) (v.adicCompletion K)) where
  carrier := localIntegralSet K v
  isCompact' := isCompact_localIntegralSet K v
  interior_nonempty' := by
    rw [(isOpen_localIntegralSet K v).interior_eq]
    exact ⟨1, one_mem_localIntegralSet K v⟩

def localHaar : @Measure (GL (Fin 2) (v.adicCompletion K)) (localGLBorel K v) := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  haveI := locallyCompactSpace_localGL K v
  exact Measure.haarMeasure (localIntegralCompacts K v)

end Local

section OrbitalIntegral

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

@[reducible] def localCentralizerBorel (γ : GL (Fin 2) (v.adicCompletion K)) :
    MeasurableSpace (localCentralizer K v γ) := borel _

def IsSectionFn (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (w : GL (Fin 2) (v.adicCompletion K) → ℝ) : Prop :=
  letI := localGLBorel K v
  letI := localCentralizerBorel K v γ
  (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
    ∀ x, fv (x⁻¹ * γ * x) ≠ 0 → ∫ t : localCentralizer K v γ, w (t * x) ∂τ = 1

def IsOrbitalIntegral (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (I : ℂ) : Prop :=
  letI := localGLBorel K v
  ∃ w : GL (Fin 2) (v.adicCompletion K) → ℝ, IsSectionFn K v γ τ fv w ∧
    I = ∫ x, fv (x⁻¹ * γ * x) * (w x : ℂ) ∂(localHaar K v)

end OrbitalIntegral

section UnitFactor

variable (K : Type) [Field K] [NumberField K]

def unitFinSet : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :=
  {h | ∀ v : HeightOneSpectrum (𝓞 K), AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v}

end UnitFactor

section Tier

variable (K : Type) [Field K] [NumberField K]

def IsBiInvariantUnder (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) : Prop :=
  ∀ u ∈ U, ∀ g, f (u * g) = f g ∧ f (g * u) = f g

def IsUnitFactorizableAt (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) : Prop :=
  IsBiInvariantUnder K U f ∧
  ∃ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
    IsArchTestFactor K fa ∧ IsFinTestFactor K ff ∧ (∀ v ∈ S, IsLocalTestFn K v (fS v)) ∧
    (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
      (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v) →
        ff h = ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v h)) ∧
    (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
      (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v h ∉ localIntegralSet K v) → ff h = 0) ∧
    ∀ g, f g = fa (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g)

def IsIntegralLevel (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))) : Prop :=
  ∀ u ∈ U, AdelicLevel.glArch (𝓞 K) K u = 1 ∧
    AdelicLevel.glFin (𝓞 K) K u ∈ AdelicLevel.finiteIntegralGL2 (𝓞 K) K

end Tier

section RegularSemisimple

variable {A : Type*} [CommRing A]

def IsRegularSemisimple (g : GL (Fin 2) A) : Prop :=
  IsUnit (Matrix.trace (g : Matrix (Fin 2) (Fin 2) A) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) A))

end RegularSemisimple

end AutomorphicForm

end
-- updated on 2026-11-16
