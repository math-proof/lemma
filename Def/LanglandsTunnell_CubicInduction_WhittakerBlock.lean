import Def.HaarQuotient
import Lemma.LanglandsTunnell.CubicInduction_Structure
import Def.NumberField_TateGlobalZeta
import Instance.M4aHerbrand_AdeleTopologyFacts
import Instance.LanglandsTunnell_CubicInduction_WhittakerBlock

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicHaar LanglandsTunnell.CubicInduction Topology
open scoped ENNReal NNReal

namespace WhittakerBlock

def unipotentSubgroup3 : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  Subgroup.closure (Set.range fun t : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
    upperUnipotent3 t.1 t.2.1 t.2.2)

def unipotentHaar3 :
    @Measure ↥unipotentSubgroup3 (@Subtype.instMeasurableSpace _ _ (glBorel (Fin 3) (𝓞 ℚ) ℚ)) :=
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := adeleBorel (𝓞 ℚ) ℚ
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := glBorel (Fin 3) (𝓞 ℚ) ℚ
  Measure.map
    (fun t : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      (⟨upperUnipotent3 t.1 t.2.1 t.2.2, Subgroup.subset_closure ⟨t, rfl⟩⟩ : unipotentSubgroup3))
    ((adelicAddHaar (𝓞 ℚ) ℚ).prod ((adelicAddHaar (𝓞 ℚ) ℚ).prod (adelicAddHaar (𝓞 ℚ) ℚ)))

def quotientMeasure :
    @Measure (MulAction.orbitRel.Quotient (unipotentSubgroup3) (AdelicGL 3 (𝓞 ℚ) ℚ))
      (@Quotient.instMeasurableSpace _ _ (glBorel (Fin 3) (𝓞 ℚ) ℚ)) :=
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := glBorel (Fin 3) (𝓞 ℚ) ℚ
  HaarQuotient.measure (adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) unipotentSubgroup3 unipotentHaar3

def zerothShell (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    Set (MulAction.orbitRel.Quotient (unipotentSubgroup3) (AdelicGL 3 (𝓞 ℚ) ℚ)) :=
  {q | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S →
    ∃ (x y z : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)),
      k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ componentAt3 (𝓞 ℚ) ℚ p q.out = upperUnipotent3 x y z * k}

def block (pins : AutomorphicForm.CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (σ : ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : ENNReal :=
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := glBorel (Fin 3) (𝓞 ℚ) ℚ
  ∫⁻ q in zerothShell S,
    ((‖whittaker3 pins ψ f q.out‖₊ : ENNReal) ^ 2 *
      (‖Φ fun j : Fin 3 => (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ENNReal) *
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det q.out) ^ σ))
    ∂quotientMeasure

end WhittakerBlock

end
