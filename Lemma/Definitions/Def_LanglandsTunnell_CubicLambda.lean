import Lemma.Definitions.Def_LanglandsTunnell_ConverseData
import Lemma.Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Lemma.Definitions.Def_HeckeCharacter_FiniteOrder

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.TateGlobal
open NumberField.StandardAddChar LanglandsTunnell.TateLocal LanglandsTunnell.RankinSelberg
open LanglandsTunnell.Converse AutomorphicForm HeckeCharacter

namespace LanglandsTunnell.CubicLambda

open scoped Classical in

noncomputable def eulerCoeff (F : Type) [Field F] [NumberField F] (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if IsUnramifiedCharAt η v then ((η (uniformizerIdele F v) : ℂˣ) : ℂ) else 0

noncomputable def zetaEulerPoly (F : Type) [Field F] [NumberField F] [Algebra (𝓞 ℚ) (𝓞 F)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 F)] (p : HeightOneSpectrum (𝓞 ℚ)) : Polynomial ℂ :=
  inducedEulerPoly ℚ (fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℂ)) p

noncomputable def resolventSignBit (L : Type) [Field L] [NumberField L] : ZMod 2 :=
  if nrComplexPlaces L = 0 then 0 else 1

inductive ResolventDatum (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] : Type 1

  | s3 (L : Type) [Field L] [NumberField L] [Algebra (𝓞 ℚ) (𝓞 L)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 L)]
      (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (θ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
      (hL : Module.finrank ℚ L = 2)
      (hω : IsFiniteOrderHeckeChar ℚ ω) (hθ : IsFiniteOrderHeckeChar L θ)
      (eulerω : ∀ p : HeightOneSpectrum (𝓞 ℚ), zetaEulerPoly L p =
        (Polynomial.C 1 - Polynomial.X) * (Polynomial.C 1 - Polynomial.C (eulerCoeff ℚ ω p) * Polynomial.X))
      (eulerθ : ∀ p : HeightOneSpectrum (𝓞 ℚ), zetaEulerPoly K p =
        (Polynomial.C 1 - Polynomial.X) * inducedEulerPoly ℚ (eulerCoeff L θ) p)
      (archω : ∀ w : InfinitePlace ℚ, IsArchCompAt ℚ ω w 0 ((resolventSignBit L).val : ℤ))
      (archθR : ∀ u : InfinitePlace L, u.IsReal → IsArchCompAt L θ u 0 (((0 : ZMod 2)).val : ℤ))
      (archθC : ∀ u : InfinitePlace L, u.IsComplex → IsArchCompAt L θ u 0 0)
      (sig : nrRealPlaces K = nrRealPlaces L + 1 ∧ nrComplexPlaces K = nrComplexPlaces L) :
      ResolventDatum K

  | cyclic (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsFiniteOrderHeckeChar ℚ χ)
      (eulerχ : ∀ p : HeightOneSpectrum (𝓞 ℚ), zetaEulerPoly K p =
        (Polynomial.C 1 - Polynomial.X) * (Polynomial.C 1 - Polynomial.C (eulerCoeff ℚ χ p) * Polynomial.X) *
          (Polynomial.C 1 - Polynomial.C (eulerCoeff ℚ (χ ^ 2) p) * Polynomial.X))
      (archχ : ∀ w : InfinitePlace ℚ, IsArchCompAt ℚ χ w 0 (((0 : ZMod 2)).val : ℤ))
      (sig : nrComplexPlaces K = 0) :
      ResolventDatum K

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

noncomputable def lambdaAt : ResolventDatum K → HeightOneSpectrum (𝓞 ℚ) → ℂ
  | @ResolventDatum.s3 _ _ _ _ _ L iF iN iA iI ω θ _ _ _ _ _ _ _ _ _, p => by
      letI := iF
      letI := iN
      letI := iA
      letI := iI
      exact stdRootNumberAt ℚ p (localChar ω p) *
        ∏ᶠ u ∈ primeFibre ℚ L p, stdRootNumberAt L u (localChar θ u)
  | .cyclic χ _ _ _ _, p =>
      stdRootNumberAt ℚ p (localChar χ p) * stdRootNumberAt ℚ p (localChar (χ ^ 2) p)

noncomputable def lambdaFin (Λd : ResolventDatum K) (w : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal = 1 ∧
      (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal = 1 then 1
  else lambdaAt K Λd (w.under (𝓞 ℚ))

open scoped Classical in

noncomputable def lambdaArch (w : InfinitePlace K) : ℂ :=
  if w.IsReal then 1 else signEpsilon 1

end LanglandsTunnell.CubicLambda
