import Def.LanglandsTunnell_ConverseData

set_option autoImplicit false

noncomputable section

open NumberField AutomorphicForm IsDedekindDomain LanglandsTunnell Polynomial
open NumberField.TateGlobal LanglandsTunnell.TateLocal LanglandsTunnell.Converse

namespace LanglandsTunnell.HeckeTate

variable (F : Type) [Field F] [NumberField F]

open Classical in

def heckeDatum (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace F, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace F, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace F, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace F, w.IsComplex → ℤ) :
    LDatum (HeightOneSpectrum (𝓞 F)) where
  norm := fun v => Ideal.absNorm v.asIdeal
  euler := fun v =>
    if IsUnramifiedCharAt χ v then C 1 - C ((χ (uniformizerIdele F v) : ℂˣ) : ℂ) * X else C 1
  dual := fun v =>
    if IsUnramifiedCharAt χ v then C 1 - C (((χ (uniformizerIdele F v))⁻¹ : ℂˣ) : ℂ) * X else C 1
  gammaR := (Finset.univ : Finset {w : InfinitePlace F // w.IsReal}).sum
    fun w => ({uR w.1 w.2 + signShift (aR w.1 w.2)} : Multiset ℂ)
  gammaC := (Finset.univ : Finset {w : InfinitePlace F // w.IsComplex}).sum
    fun w => ({uC w.1 w.2 + ((kC w.1 w.2).natAbs : ℂ) / 2} : Multiset ℂ)
  gammaRDual := (Finset.univ : Finset {w : InfinitePlace F // w.IsReal}).sum
    fun w => ({-uR w.1 w.2 + signShift (aR w.1 w.2)} : Multiset ℂ)
  gammaCDual := (Finset.univ : Finset {w : InfinitePlace F // w.IsComplex}).sum
    fun w => ({-uC w.1 w.2 + ((-kC w.1 w.2).natAbs : ℂ) / 2} : Multiset ℂ)
  abscissa := 1
  center := 1 / 2
  degree := 1

open Classical in

def heckeRootNumber (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (aR : ∀ w : InfinitePlace F, w.IsReal → ZMod 2) (kC : ∀ w : InfinitePlace F, w.IsComplex → ℤ) : ℂ :=
  ((Finset.univ : Finset {w : InfinitePlace F // w.IsReal}).prod fun w => signEpsilon (aR w.1 w.2)) *
    ((Finset.univ : Finset {w : InfinitePlace F // w.IsComplex}).prod
      fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), stdRootNumberAt F v (localChar χ v)

def heckeConductor (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), (Ideal.absNorm v.asIdeal : ℝ) ^ (pinnedExp F χ v)

end LanglandsTunnell.HeckeTate

end
