import Def.LanglandsTunnell_StandardLocalConstantsAt
import Def.LanglandsTunnell_ArchEpsilon
import Lemma.LanglandsTunnell.HonestLDatum
import Def.NumberField_TateGlobalZeta
import Lemma.AutomorphicForm.HeckeEigenfunction

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.Converse

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal NumberField.StandardAddChar LanglandsTunnell.TateLocal

variable (K : Type) [Field K] [NumberField K]

def pinnedExp (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : ℤ :=
  (conductorExponentAt K v (localChar μ v) : ℤ) + addCharLevel (psiLocal K v)

def goodPlaceRootNumber (Pi : HeckeEigensystem K ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  (Pi.b v : ℂ) ^ (pinnedExp K μ v) * (stdRootNumberAt K v (localChar μ v)) ^ 2

open Classical in

def finiteRootNumber (Pi : HeckeEigensystem K ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : ℂ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), if v ∈ S then 1 else goodPlaceRootNumber K Pi μ v

open Classical in

def finiteConductor (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    if v ∈ S then 1 else (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * pinnedExp K μ v)

open Classical in

def archRootNumber (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) : ℂ :=
  ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
      fun w => ((archR w.1 w.2).twist (uR w.1 w.2) (aR w.1 w.2)).epsilonFactor) *
    ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
      fun w => ((archC w.1 w.2).twist (uC w.1 w.2) (kC w.1 w.2)).epsilonFactor)

def pinnedRootNumber (Pi : HeckeEigensystem K ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) : ℂ :=
  archRootNumber K archR archC uR aR uC kC * finiteRootNumber K Pi μ S

end LanglandsTunnell.Converse

end

noncomputable section

open NumberField AutomorphicForm IsDedekindDomain LanglandsTunnell Polynomial
open NumberField.TateGlobal NumberField.InfinitePlace.Completion

namespace LanglandsTunnell.Converse

variable (K : Type) [Field K] [NumberField K] (Pi : HeckeEigensystem K ℂ)

def IsAdmissibleTwist (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : Prop :=
  IsIdeleClassChar (𝓞 K) K μ ∧ Continuous μ ∧ IsUnitaryChar (𝓞 K) K μ

def IsArchCompAt (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : InfinitePlace K)
    (u : ℂ) (a : ℤ) : Prop :=
  ∀ x : (w.Completion)ˣ,
    ((archLocalChar μ w x : ℂˣ) : ℂ) =
      ((‖(x : w.Completion)‖ : ℂ) ^ ((w.mult : ℂ) * u)) *
        (extensionEmbedding w (x : w.Completion) / (‖(x : w.Completion)‖ : ℂ)) ^ a

open Classical in

def twistedGammaR (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2) :
    Multiset ℂ :=
  (Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).sum
    fun w => ((archR w.1 w.2).twist (uR w.1 w.2) (aR w.1 w.2)).gammaR

open Classical in

def twistedGammaC (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) :
    Multiset ℂ :=
  ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).sum
      fun w => ((archR w.1 w.2).twist (uR w.1 w.2) (aR w.1 w.2)).gammaC) +
    ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).sum
      fun w => ((archC w.1 w.2).twist (uC w.1 w.2) (kC w.1 w.2)).gammaC)

def twistedDatum (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) :
    LDatum {v : HeightOneSpectrum (𝓞 K) // v ∉ S} where
  norm := fun v => Ideal.absNorm v.1.asIdeal
  euler := open scoped Classical in fun v =>
    if IsUnramifiedCharAt μ v.1
    then C 1 - C (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) * Pi.a v.1) * X
      + C ((((μ (uniformizerIdele K v.1))^2 : ℂˣ) : ℂ) * Pi.b v.1) * X ^ 2
    else C 1
  dual := open scoped Classical in fun v =>
    if IsUnramifiedCharAt μ v.1
    then C 1 - C ((((μ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) * (Pi.a v.1 / Pi.b v.1)) * X
      + C ((((μ (uniformizerIdele K v.1))^(-2 : ℤ) : ℂˣ) : ℂ) * (Pi.b v.1)⁻¹) * X ^ 2
    else C 1
  gammaR := twistedGammaR K archR uR aR
  gammaC := twistedGammaC K archR archC uR aR uC kC
  gammaRDual := twistedGammaR K (fun w hw => (archR w hw).dual) (fun w hw => -uR w hw) aR
  gammaCDual := twistedGammaC K (fun w hw => (archR w hw).dual)
    (fun w hw => (archC w hw).dual) (fun w hw => -uR w hw) aR
    (fun w hw => -uC w hw) (fun w hw => -kC w hw)
  abscissa := 1
  center := 1 / 2
  degree := 2

def eisensteinTableOf (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (μ₁ μ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : HeckeEigensystem K ℂ where
  level := N
  level_ne_bot := hN
  a := fun v => ((μ₁ (uniformizerIdele K v) : ℂˣ) : ℂ) + ((μ₂ (uniformizerIdele K v) : ℂˣ) : ℂ)
  b := fun v => ((μ₁ (uniformizerIdele K v) : ℂˣ) : ℂ) * ((μ₂ (uniformizerIdele K v) : ℂˣ) : ℂ)

def IsNicePinned {ι : Type*} (D : LDatum ι) (ΛS ΛSd : ℂ → ℂ) (ε : ℂ) (N : ℝ) : Prop :=
  D.WellFormed ∧ D.Converges ∧ 0 < N ∧
  ∃ Λ Λd : ℂ → ℂ,
    Differentiable ℂ Λ ∧ Differentiable ℂ Λd ∧
    LDatum.BoundedOnStrips Λ ∧ LDatum.BoundedOnStrips Λd ∧
    (∀ s : ℂ, D.abscissa < s.re → Λ s = ΛS s * D.archFactor s * D.LFun s) ∧
    (∀ s : ℂ, D.abscissa < s.re → Λd s = ΛSd s * D.archFactorDual s * D.LFunDual s) ∧
    (∀ s : ℂ, Λ s = ε * (N : ℂ) ^ ((D.center : ℂ) - s) * Λd (2 * (D.center : ℂ) - s))

def sPart (S : Finset (HeightOneSpectrum (𝓞 K))) (A : (↥S → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∑' n : ↥S → ℤ, A n * ∏ v : ↥S,
    (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n v)

def sPartDual (S : Finset (HeightOneSpectrum (𝓞 K))) (Ad : (↥S → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∑' n : ↥S → ℤ, Ad n * ∏ v : ↥S,
    ((((μ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n v)

end LanglandsTunnell.Converse

end
