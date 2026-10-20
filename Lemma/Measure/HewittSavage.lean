import Mathlib
import sympy.Basic
import sympy.atlas.Probability.HewittSavage
open MeasureTheory
open scoped ENNReal
open MathlibExt.Probability.HewittSavageWanted


/--
[hewitt_savage_zero_one_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/HewittSavage.lean)
-/
@[path]
private lemma hewitt_savage_zero_one_general_eq
  [MeasurableSpace S]
  {μ : Measure S} [IsProbabilityMeasure μ]
  {E : Set (ℕ → S)}
-- given
  (hE : MeasurableSet E)
  (hSym : ∀ (σ : Equiv.Perm ℕ), Set.Finite {n : ℕ | σ n ≠ n} → (fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' E = E) :
-- imply
  Measure.infinitePi (fun _ : ℕ => μ) E = 0 ∨
    Measure.infinitePi (fun _ : ℕ => μ) E = 1 := by
-- proof
  apply MathlibExt.Probability.HewittSavageWanted.hewitt_savage_zero_one_general μ E hE hSym

/--
[hewitt_savage_zero_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/HewittSavage.lean)
-/
@[path]
private lemma hewitt_savage_zero_one_eq
  [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
  {μ : Measure S} [IsProbabilityMeasure μ]
  {E : Set (ℕ → S)}
-- given
  (hE : MeasurableSet E)
  (hSym : ∀ (σ : Equiv.Perm ℕ), Set.Finite {n : ℕ | σ n ≠ n} → (fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' E = E) :
-- imply
  Measure.infinitePi (fun _ : ℕ => μ) E = 0 ∨
    Measure.infinitePi (fun _ : ℕ => μ) E = 1 := by
-- proof
  apply MathlibExt.Probability.HewittSavageWanted.hewitt_savage_zero_one μ E hE hSym


-- created on 2026-10-20
