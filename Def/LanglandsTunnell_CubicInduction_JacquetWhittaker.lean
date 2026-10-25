import Lemma.LanglandsTunnell.CubicInduction_PrincipalSeries3
import Def.LanglandsTunnell_StandardLocalConstantsAt

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

namespace LanglandsTunnell.CubicInduction

section Jacquet

variable (v : HeightOneSpectrum (𝓞 ℚ))

def unipotentBall3 (c : ℤ) : Set (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :=
  {p | Valued.v p.1 ≤ WithZero.exp c ∧ Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp (2 * c)}


def jacquetHaar3 :
    @Measure (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ)
      (@Prod.instMeasurableSpace _ _ (localBorel ℚ v)
        (@Prod.instMeasurableSpace _ _ (localBorel ℚ v) (localBorel ℚ v))) := by
  letI := localBorel ℚ v
  exact (selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))


def jacquetTruncated3 (c : ℤ) (u : LocalGL3 v → ℂ) : ℂ := by
  letI := localBorel ℚ v
  exact ∫ p in unipotentBall3 v c,
    psiLocal ℚ v (-(p.1 + p.2.1)) * u (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2) ∂(jacquetHaar3 v)


def jacquetLevel (u : LocalGL3 v → ℂ) : ℕ :=
  sInf {c₀ : ℕ | ∀ c : ℤ, (c₀ : ℤ) ≤ c → jacquetTruncated3 v c u = jacquetTruncated3 v c₀ u}

def jacquetValue (u : LocalGL3 v → ℂ) : ℂ :=
  jacquetTruncated3 v (jacquetLevel v u) u


def bigCell3 : Set (LocalGL3 v) :=
  {g | cornerEntry v g ≠ 0 ∧ lowerMinor v g ≠ 0}


def cellSectionOf (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) :
    LocalGL3 v → ℂ :=
  (bigCell3 v).indicator fun g => cellValue v χ g * Φ (cellRatio v g)


def jacquetWhittaker3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) :
    LocalGL3 v → ℂ :=
  fun g => jacquetValue v (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v χ Φ))

end Jacquet

end LanglandsTunnell.CubicInduction

end
