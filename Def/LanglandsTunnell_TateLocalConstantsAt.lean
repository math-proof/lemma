import Def.LanglandsTunnell_TateLocalZeta
import Lemma.NumberField.AdelicLevel

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.TateLocal

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

def higherUnitsAt (n : ℕ) : Set (v.adicCompletion K)ˣ :=
  {u | Valued.v (u : v.adicCompletion K) = 1 ∧
    (n = 0 ∨ Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ)))}


def HasConductorExponentAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ) : Prop :=
  (∀ u ∈ higherUnitsAt K v c, χ u = 1) ∧ ∀ m < c, ∃ u ∈ higherUnitsAt K v m, χ u ≠ 1


def conductorExponentAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) : ℕ :=
  sInf {c | HasConductorExponentAt K v χ c}


open Classical in

def localLFactorAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  if HasConductorExponentAt K v χ 0 then
    (1 - (χ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹
  else 1


section Epsilon

variable [MeasurableSpace (v.adicCompletion K)]

def localEpsilonAt (μ : Measure (v.adicCompletion K)) (ψ : AddChar (v.adicCompletion K) ℂ)
    (f : v.adicCompletion K → ℂ) (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  localGammaAt μ ψ f χ s * localLFactorAt K v χ s / localLFactorAt K v χ⁻¹ (1 - s)

end Epsilon

end LanglandsTunnell.TateLocal

end
