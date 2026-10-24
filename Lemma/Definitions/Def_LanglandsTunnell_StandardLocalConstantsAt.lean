import Lemma.Definitions.Def_NumberField_AdelicTraceFin
import Lemma.Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

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

open scoped Classical in
theorem finAdeleSingleAt_apply_self (x : v.adicCompletion K) : finAdeleSingleAt K v x v = x :=
  RestrictedProduct.single_eq_same _ v x

open scoped Classical in
theorem finAdeleSingleAt_apply_of_ne (x : v.adicCompletion K) {w : HeightOneSpectrum (𝓞 K)}
    (h : w ≠ v) : finAdeleSingleAt K v x w = 0 :=
  RestrictedProduct.single_eq_of_ne _ x h

open scoped Classical in

theorem continuous_finAdeleSingleAt : Continuous (finAdeleSingleAt K v) := by
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 K))) ≤ Filter.principal ({v}ᶜ) :=
    Filter.le_principal_iff.mpr (Set.finite_singleton v).compl_mem_cofinite
  let e : v.adicCompletion K →
      RestrictedProduct (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
        (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) (Filter.principal ({v}ᶜ)) :=
    fun x => ⟨Pi.single v x, by
      rw [Filter.eventually_principal]
      intro w hw
      rw [Pi.single_eq_of_ne (by simpa using hw)]
      exact zero_mem _⟩
  have he : Continuous e := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_single v
  have hfun : (fun x => finAdeleSingleAt K v x)
      = fun x => (RestrictedProduct.inclusion _ _ hle (e x) : FiniteAdeleRing (𝓞 K) K) := by
    funext x
    exact FiniteAdeleRing.ext K fun w => rfl
  change Continuous (fun x => finAdeleSingleAt K v x)
  rw [hfun]
  exact (RestrictedProduct.continuous_inclusion hle).comp he

def adeleSingleAt : v.adicCompletion K →+ AdeleRing (𝓞 K) K :=
  (AddMonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp (finAdeleSingleAt K v)

theorem adeleSingleAt_apply (x : v.adicCompletion K) :
    adeleSingleAt K v x = ((0 : InfiniteAdeleRing K), finAdeleSingleAt K v x) := rfl

theorem continuous_adeleSingleAt : Continuous (adeleSingleAt K v) :=
  continuous_const.prodMk (continuous_finAdeleSingleAt K v)

def psiLocal : AddChar (v.adicCompletion K) ℂ :=
  (stdAddChar K).compAddMonoidHom (adeleSingleAt K v)

theorem psiLocal_apply (x : v.adicCompletion K) :
    psiLocal K v x = stdAddChar K ((0 : InfiniteAdeleRing K), finAdeleSingleAt K v x) := rfl

theorem continuous_psiLocal : Continuous (psiLocal K v) :=
  (adelicTraceData K).continuous_psiK.comp (continuous_adeleSingleAt K v)

end NumberField.StandardAddChar

namespace LanglandsTunnell.TateLocal

open NumberField.StandardAddChar

section Level

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

def addCharLevel (ψ : AddChar (v.adicCompletion K) ℂ) : ℤ :=
  sSup {n : ℤ | ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1}

theorem addCharLevel_def (ψ : AddChar (v.adicCompletion K) ℂ) :
    addCharLevel ψ
      = sSup {n : ℤ | ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1} := rfl

end Level

section Std

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

@[reducible] def localBorel : MeasurableSpace (v.adicCompletion K) := borel _

theorem borelSpace_localBorel : @BorelSpace (v.adicCompletion K) _ (localBorel K v) :=
  @BorelSpace.mk _ _ (localBorel K v) rfl

def integersPositiveCompacts : TopologicalSpace.PositiveCompacts (v.adicCompletion K) where
  carrier := (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  isCompact' := isCompact_iff_compactSpace.mpr
    (show CompactSpace (v.adicCompletionIntegers K) from inferInstance)
  interior_nonempty' := by
    have h : IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
      Valued.isOpen_valuationSubring _
    rw [h.interior_eq]
    exact ⟨0, (v.adicCompletionIntegers K).zero_mem⟩

theorem coe_integersPositiveCompacts :
    (integersPositiveCompacts K v : Set (v.adicCompletion K)) = v.adicCompletionIntegers K := rfl

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

theorem stdRootNumberAt_def (χ : (v.adicCompletion K)ˣ →* ℂˣ) :
    stdRootNumberAt K v χ = stdEpsilonAt K v χ (1 / 2) := rfl

end Std

end LanglandsTunnell.TateLocal

end
