import Lemma.NumberField.AdelicTraceFin
import Lemma.LanglandsTunnell.TateLocalConstantsAt
import Def.LanglandsTunnell_StandardLocalConstantsAt

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory
open scoped NNReal

namespace NumberField.StandardAddChar

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))


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


theorem adeleSingleAt_apply (x : v.adicCompletion K) :
    adeleSingleAt K v x = ((0 : InfiniteAdeleRing K), finAdeleSingleAt K v x) := rfl

theorem continuous_adeleSingleAt : Continuous (adeleSingleAt K v) :=
  continuous_const.prodMk (continuous_finAdeleSingleAt K v)


theorem psiLocal_apply (x : v.adicCompletion K) :
    psiLocal K v x = stdAddChar K ((0 : InfiniteAdeleRing K), finAdeleSingleAt K v x) := rfl

theorem continuous_psiLocal : Continuous (psiLocal K v) :=
  (adelicTraceData K).continuous_psiK.comp (continuous_adeleSingleAt K v)

end NumberField.StandardAddChar

namespace LanglandsTunnell.TateLocal

open NumberField.StandardAddChar

section Level

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}


theorem addCharLevel_def (ψ : AddChar (v.adicCompletion K) ℂ) :
    addCharLevel ψ
      = sSup {n : ℤ | ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1} := rfl

end Level

section Std

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))


theorem borelSpace_localBorel : @BorelSpace (v.adicCompletion K) _ (localBorel K v) :=
  @BorelSpace.mk _ _ (localBorel K v) rfl


theorem coe_integersPositiveCompacts :
    (integersPositiveCompacts K v : Set (v.adicCompletion K)) = v.adicCompletionIntegers K := rfl


theorem stdRootNumberAt_def (χ : (v.adicCompletion K)ˣ →* ℂˣ) :
    stdRootNumberAt K v χ = stdEpsilonAt K v χ (1 / 2) := rfl

end Std

end LanglandsTunnell.TateLocal

end
