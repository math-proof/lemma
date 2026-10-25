import Def.LanglandsTunnell_CubicInduction_GlobalZeta31

set_option autoImplicit false

open Matrix NumberField MeasureTheory IsDedekindDomain

noncomputable section

namespace LanglandsTunnell.CubicInduction

section FinitePlace

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable {mT : MeasurableSpace (v.adicCompletion ℚ)ˣ} {mA : MeasurableSpace (v.adicCompletion ℚ)}

def localZeta31 (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) (W : LocalGL3 v → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v) : ℂ :=
  ∫ a : (v.adicCompletion ℚ)ˣ,
      (∫ x : v.adicCompletion ℚ, W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) ∂ν) *
        ((χ a : ℂˣ) : ℂ) * ((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)
    ∂μ

def localZeta30 (μ : Measure (v.adicCompletion ℚ)ˣ) (W : LocalGL3 v → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (s : ℂ) (g : LocalGL3 v) : ℂ :=
  ∫ a : (v.adicCompletion ℚ)ˣ,
      W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) *
        ((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)
    ∂μ

def localZetaDual31 (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) (W : LocalGL3 v → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v) : ℂ :=
  localZeta31 v μ ν (dualWhittakerFn3 W) χ⁻¹ s (weylPrime3 * transposeInv3 g)

def IsLocalZeta30ConvergentAbove (μ : Measure (v.adicCompletion ℚ)ˣ) (W : LocalGL3 v → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 v) (σ₀ : ℝ) : Prop :=
  ∀ s : ℂ, σ₀ < s.re →
    Integrable (fun a : (v.adicCompletion ℚ)ˣ =>
      W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) *
        ((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) μ

def IsLocalZeta31ConvergentAbove (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ))
    (W : LocalGL3 v → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 v) (σ₀ : ℝ) : Prop :=
  ∀ s : ℂ, σ₀ < s.re →
    Integrable (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
      W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * g) * ((χ p.1 : ℂˣ) : ℂ) *
        ((TateLocal.modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) (μ.prod ν)

end FinitePlace

end LanglandsTunnell.CubicInduction

end
