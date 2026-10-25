import Lemma.NumberField.AdelicTraceFin
import Def.LanglandsTunnell_TateLocalConstantsAt

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory
open scoped NNReal

namespace NumberField.StandardAddChar

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open scoped Classical in

def finAdeleSingleAt : v.adicCompletion K →+ FiniteAdeleRing (𝓞 K) K where
  toFun x := (RestrictedProduct.single
    (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K) v x : FiniteAdeleRing (𝓞 K) K)
  map_zero' := RestrictedProduct.single_zero _ v
  map_add' x y := RestrictedProduct.single_add _ v x y


def adeleSingleAt : v.adicCompletion K →+ AdeleRing (𝓞 K) K :=
  (AddMonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp (finAdeleSingleAt K v)


def psiLocal : AddChar (v.adicCompletion K) ℂ :=
  (stdAddChar K).compAddMonoidHom (adeleSingleAt K v)

end NumberField.StandardAddChar

namespace LanglandsTunnell.TateLocal

open NumberField.StandardAddChar

section Level

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

def addCharLevel (ψ : AddChar (v.adicCompletion K) ℂ) : ℤ :=
  sSup {n : ℤ | ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1}

end Level

section Std

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

@[reducible] def localBorel : MeasurableSpace (v.adicCompletion K) := borel _


def integersPositiveCompacts : TopologicalSpace.PositiveCompacts (v.adicCompletion K) where
  carrier := (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  isCompact' := isCompact_iff_compactSpace.mpr
    (show CompactSpace (v.adicCompletionIntegers K) from inferInstance)
  interior_nonempty' := by
    have h : IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
      Valued.isOpen_valuationSubring _
    rw [h.interior_eq]
    exact ⟨0, (v.adicCompletionIntegers K).zero_mem⟩


def selfDualHaarAt : @Measure (v.adicCompletion K) (localBorel K v) := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  exact ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (psiLocal K v) : ℝ) / 2))
    • Measure.addHaarMeasure (integersPositiveCompacts K v)

open Classical in

def stdTestFunAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) : v.adicCompletion K → ℂ :=
  if HasConductorExponentAt K v χ 0 then
    (v.adicCompletionIntegers K : Set (v.adicCompletion K)).indicator fun _ => (1 : ℂ)
  else
    (((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) ''
        higherUnitsAt K v (conductorExponentAt K v χ)).indicator fun _ => (1 : ℂ)

def stdEpsilonAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) : ℂ := by
  letI := localBorel K v
  exact localEpsilonAt K v (selfDualHaarAt K v) (psiLocal K v) (stdTestFunAt K v χ) χ s

def stdRootNumberAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) : ℂ :=
  stdEpsilonAt K v χ (1 / 2)

end Std

end LanglandsTunnell.TateLocal

end
