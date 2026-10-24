import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_Growth

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Sizes

variable {L : Type*} [NormedField L]

def lastRowSup (k : GL (Fin 3) L) : ℝ :=
  max (max ‖(k : Matrix (Fin 3) (Fin 3) L) 2 0‖ ‖(k : Matrix (Fin 3) (Fin 3) L) 2 1‖)
    ‖(k : Matrix (Fin 3) (Fin 3) L) 2 2‖

def bottomMinor (k : GL (Fin 3) L) (j j' : Fin 3) : L :=
  (k : Matrix (Fin 3) (Fin 3) L) 1 j * (k : Matrix (Fin 3) (Fin 3) L) 2 j' -
    (k : Matrix (Fin 3) (Fin 3) L) 1 j' * (k : Matrix (Fin 3) (Fin 3) L) 2 j

def minorSup (k : GL (Fin 3) L) : ℝ :=
  max (max ‖bottomMinor k 0 1‖ ‖bottomMinor k 0 2‖) ‖bottomMinor k 1 2‖

def lastRowEucl (k : GL (Fin 3) L) : ℝ :=
  Real.sqrt (‖(k : Matrix (Fin 3) (Fin 3) L) 2 0‖ ^ 2 + ‖(k : Matrix (Fin 3) (Fin 3) L) 2 1‖ ^ 2 +
    ‖(k : Matrix (Fin 3) (Fin 3) L) 2 2‖ ^ 2)

def minorEucl (k : GL (Fin 3) L) : ℝ :=
  Real.sqrt (‖bottomMinor k 0 1‖ ^ 2 + ‖bottomMinor k 0 2‖ ^ 2 + ‖bottomMinor k 1 2‖ ^ 2)

def detSize (k : GL (Fin 3) L) : ℝ :=
  ‖(k : Matrix (Fin 3) (Fin 3) L).det‖

end Sizes

section Roots

variable (F : Type) [Field F] [NumberField F]

def finRoot₁ (v : HeightOneSpectrum (𝓞 F)) (g : AdelicGL 3 (𝓞 F) F) : ℝ :=
  detSize (componentAt3 (𝓞 F) F v g) * lastRowSup (componentAt3 (𝓞 F) F v g) /
    minorSup (componentAt3 (𝓞 F) F v g) ^ 2

def finRoot₂ (v : HeightOneSpectrum (𝓞 F)) (g : AdelicGL 3 (𝓞 F) F) : ℝ :=
  minorSup (componentAt3 (𝓞 F) F v g) / lastRowSup (componentAt3 (𝓞 F) F v g) ^ 2

def archRoot₁ (w : InfinitePlace F) (g : AdelicGL 3 (𝓞 F) F) : ℝ :=
  detSize (archPlaceComponent3 F w g) * lastRowEucl (archPlaceComponent3 F w g) /
    minorEucl (archPlaceComponent3 F w g) ^ 2

def archRoot₂ (w : InfinitePlace F) (g : AdelicGL 3 (𝓞 F) F) : ℝ :=
  minorEucl (archPlaceComponent3 F w g) / lastRowEucl (archPlaceComponent3 F w g) ^ 2

def rootSizeProd (g : AdelicGL 3 (𝓞 F) F) : ℝ :=
  (∏ᶠ v : HeightOneSpectrum (𝓞 F), finRoot₁ F v g * finRoot₂ F v g) *
    ∏ w : InfinitePlace F, archRoot₁ F w g * archRoot₂ F w g

def archRootSum (g : AdelicGL 3 (𝓞 F) F) : ℝ :=
  ∑ w : InfinitePlace F, (archRoot₁ F w g + archRoot₂ F w g)

def InRootLevel (T : Finset (HeightOneSpectrum (𝓞 F))) (B : ℝ) (g : AdelicGL 3 (𝓞 F) F) : Prop :=
  (∀ v, v ∉ T → finRoot₁ F v g ≤ 1 ∧ finRoot₂ F v g ≤ 1) ∧
    ∀ v ∈ T, finRoot₁ F v g ≤ B ∧ finRoot₂ F v g ≤ B

def IsGaugeMajorised3 (W : AdelicGL 3 (𝓞 F) F → ℂ) : Prop :=
  ∃ (t : ℕ) (T : Finset (HeightOneSpectrum (𝓞 F))) (B : ℝ), ∀ N : ℕ, ∃ C : ℝ,
    ∀ g : AdelicGL 3 (𝓞 F) F,
      (¬ InRootLevel F T B g → W g = 0) ∧
        (InRootLevel F T B g → ‖W g‖ ≤ C / (rootSizeProd F g ^ t * (1 + archRootSum F g) ^ N))

theorem isGaugeMajorised3_zero : IsGaugeMajorised3 F (fun _ => (0 : ℂ)) :=
  ⟨0, ∅, 1, fun N => ⟨0, fun g => ⟨fun _ => rfl, fun _ => by simp⟩⟩⟩

end Roots

end LanglandsTunnell.CubicInduction
