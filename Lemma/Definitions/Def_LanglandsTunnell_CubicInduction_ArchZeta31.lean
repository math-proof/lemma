import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31

set_option autoImplicit false

open Matrix NumberField MeasureTheory

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Archimedean

variable {mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ} {mA : MeasurableSpace (InfiniteAdeleRing ℚ)}

def archZeta31 (μ : Measure (InfiniteAdeleRing ℚ)ˣ) (ν : Measure (InfiniteAdeleRing ℚ))
    (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (σ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) (s : ℂ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : ℂ :=
  ∫ a : (InfiniteAdeleRing ℚ)ˣ,
      (∫ x : InfiniteAdeleRing ℚ, W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) ∂ν) *
        ((σ a : ℂˣ) : ℂ) * ((‖(a : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)
    ∂μ

def archZeta30 (μ : Measure (InfiniteAdeleRing ℚ)ˣ) (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (σ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) (s : ℂ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : ℂ :=
  ∫ a : (InfiniteAdeleRing ℚ)ˣ,
      W (iotaGL (diagUnitGL2 a) * g) * ((σ a : ℂˣ) : ℂ) *
        ((‖(a : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)
    ∂μ

def archZetaDual31 (μ : Measure (InfiniteAdeleRing ℚ)ˣ) (ν : Measure (InfiniteAdeleRing ℚ))
    (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (σ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) (s : ℂ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : ℂ :=
  archZeta31 μ ν (dualWhittakerFn3 W) σ⁻¹ s (weylPrime3 * transposeInv3 g)

def IsArchZeta30ConvergentAbove (μ : Measure (InfiniteAdeleRing ℚ)ˣ)
    (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (σ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ₀ : ℝ) : Prop :=
  ∀ s : ℂ, σ₀ < s.re →
    Integrable (fun a : (InfiniteAdeleRing ℚ)ˣ =>
      W (iotaGL (diagUnitGL2 a) * g) * ((σ a : ℂˣ) : ℂ) *
        ((‖(a : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)) μ

def IsArchZeta31ConvergentAbove (μ : Measure (InfiniteAdeleRing ℚ)ˣ) (ν : Measure (InfiniteAdeleRing ℚ))
    (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (σ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ₀ : ℝ) : Prop :=
  ∀ s : ℂ, σ₀ < s.re →
    Integrable (fun p : (InfiniteAdeleRing ℚ)ˣ × InfiniteAdeleRing ℚ =>
      W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * g) * ((σ p.1 : ℂˣ) : ℂ) *
        ((‖(p.1 : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)) (μ.prod ν)

end Archimedean

end LanglandsTunnell.CubicInduction

end
