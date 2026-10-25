import Lemma.LanglandsTunnell.CubicInduction_Carrier
import Lemma.NumberField.TateGlobalZeta
import Lemma.NumberField.AdelicLevel
import Lemma.IsDedekindDomain.FiniteUnitIdeles
import Notation.LanglandsTunnell_CubicInduction_AdelicEpstein

set_option autoImplicit false

noncomputable section

open NumberField MeasureTheory LanglandsTunnell.CubicInduction

namespace LanglandsTunnell.CubicInduction.AdelicEpstein

open scoped LanglandsTunnell_CubicInduction_AdelicEpstein

def ofReal (t : ℝ) : Rat.infinitePlace.Completion :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm t

def archIdele (t : ℝ) : 𝔸ˣ :=
  if h : t = 0 then 1 else
    TateGlobal.archUnitHom Rat.infinitePlace (Units.mk0 (ofReal t) (by unfold ofReal; exact (map_ne_zero _).mpr h))

def finUnitIdele (u : Ẑˣ) : 𝔸ˣ :=
  Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ) (u : (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)

def adelicDiag (ξ : Fin 3 → ℚ) : Fin 3 → 𝔸 := fun i => algebraMap ℚ 𝔸 (ξ i)

def point (t : ℝ) (u : Ẑˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (ξ : Fin 3 → ℚ) : Fin 3 → 𝔸 :=
  fun i => ((archIdele t * finUnitIdele u : 𝔸ˣ) : 𝔸) * (Matrix.vecMul (adelicDiag ξ) (g : Matrix (Fin 3) (Fin 3) 𝔸)) i

def scaleMeasure : Measure ℝ :=
  (volume.restrict (Set.Ioi (0 : ℝ))).withDensity fun t => ENNReal.ofReal t⁻¹

def latticeSum (Φ : (Fin 3 → 𝔸) → ℂ) (t : ℝ) (u : Ẑˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ :=
  ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, Φ (point t u g ξ)

def epstein [MeasurableSpace Ẑˣ] (du : Measure Ẑˣ) (Φ : (Fin 3 → 𝔸) → ℂ) (σ : ℝ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ :=
  ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ : ℝ) : ℂ) *
    ∫ t, ((t ^ (3 * σ) : ℝ) : ℂ) * ∫ u, latticeSum Φ t u g ∂du ∂scaleMeasure

def epsteinPlus [MeasurableSpace Ẑˣ] (du : Measure Ẑˣ) (Φ : (Fin 3 → 𝔸) → ℂ) (σ : ℝ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ENNReal :=
  ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ) *
    ∫⁻ t, ENNReal.ofReal (t ^ (3 * σ)) *
      ∫⁻ u, ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (point t u g ξ)‖₊ : ENNReal) ∂du ∂scaleMeasure

@[reducible] def unitIdeleMeasurableSpace : MeasurableSpace Ẑˣ :=
  MeasurableSpace.comap (fun u : Ẑˣ => ((finUnitIdele u : 𝔸ˣ) : 𝔸)) (NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ)

theorem measurable_finUnitIdele :
    @Measurable Ẑˣ 𝔸 unitIdeleMeasurableSpace (NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ)
      (fun u : Ẑˣ => ((finUnitIdele u : 𝔸ˣ) : 𝔸)) :=
  comap_measurable _

end LanglandsTunnell.CubicInduction.AdelicEpstein

end
