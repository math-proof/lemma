import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.BeffaraDC.AnimalLLNas.Part3
open MeasureTheory Filter Topology Finset StatMech.Kingman StatMech.KingmanAE StatMech.KingmanFilling StatMech StatMech.BeffaraDC


/--
[shiftEnv_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean)
-/
@[path]
private lemma shiftEnv_iterate_eq
  {ω : ℤ → ℝ}
  {m : ℕ}
  {i : ℤ} :
-- imply
  (shiftEnv^[m] ω) i = ω (i + m) := by
-- proof
  apply StatMech.BeffaraDC.shiftEnv_iterate ω m i

/--
[shiftEnv_eq_piCongrLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean)
-/
@[path]
private lemma shiftEnv_eq_piCongrLeft_eq :
-- imply
  shiftEnv = ⇑(Equiv.piCongrLeft (fun _ : ℤ => ℝ) (Equiv.addRight (-1 : ℤ))) := by
-- proof
  apply StatMech.BeffaraDC.shiftEnv_eq_piCongrLeft

/--
[shiftEnv_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean)
-/
@[path]
private lemma shiftEnv_measurePreserving_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ] :
-- imply
  MeasurePreserving shiftEnv (Measure.infinitePi (fun _ : ℤ => ρ)) (Measure.infinitePi (fun _ : ℤ => ρ)) := by
-- proof
  apply StatMech.BeffaraDC.shiftEnv_measurePreserving ρ

/--
[prefix_le_animalValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean)
-/
@[path]
private lemma prefix_le_animalValue_eq
  {ω : ℤ → ℝ}
  {n : ℕ}
  {a : ℕ}
-- given
  (ha : a ≤ n) :
-- imply
  (∑ i ∈ range a, ω (i : ℤ)) ≤ animalValue ω n := by
-- proof
  apply StatMech.BeffaraDC.prefix_le_animalValue n ha

/--
[animalValue_le_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean)
-/
@[path]
private lemma animalValue_le_iff_eq
  {ω : ℤ → ℝ}
  {n : ℕ}
  {c : ℝ} :
-- imply
  animalValue ω n ≤ c ↔ ∀ a ≤ n, (∑ i ∈ range a, ω (i : ℤ)) ≤ c := by
-- proof
  apply StatMech.BeffaraDC.animalValue_le_iff

/--
[animalValue_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean)
-/
@[path]
private lemma animalValue_nonneg_eq
  {ω : ℤ → ℝ}
  {n : ℕ} :
-- imply
  0 ≤ animalValue ω n := by
-- proof
  apply StatMech.BeffaraDC.animalValue_nonneg ω n

/--
[animalValue_subadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean)
-/
@[path]
private lemma animalValue_subadditive_eq
  {ω : ℤ → ℝ}
  {m n : ℕ} :
-- imply
  animalValue ω (m + n) ≤ animalValue ω m + animalValue (shiftEnv^[m] ω) n := by
-- proof
  apply StatMech.BeffaraDC.animalValue_subadditive ω m n

/--
[animalValue_le_posSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean)
-/
@[path]
private lemma animalValue_le_posSum_eq
  {ω : ℤ → ℝ}
  {n : ℕ} :
-- imply
  animalValue ω n ≤ ∑ i ∈ range n, (ω (i : ℤ))⁺ := by
-- proof
  apply StatMech.BeffaraDC.animalValue_le_posSum ω n

/--
[measurable_animalValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean)
-/
@[path]
private lemma measurable_animalValue_eq
  {n : ℕ} :
-- imply
  Measurable (fun ω : ℤ → ℝ => animalValue ω n) := by
-- proof
  apply StatMech.BeffaraDC.measurable_animalValue n

/--
[integrable_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean)
-/
@[path]
private lemma integrable_coord_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ]
  {i : ℤ}
-- given
  (hρ : Integrable (id : ℝ → ℝ) ρ) :
-- imply
  Integrable (fun ω : ℤ → ℝ => ω i) (Measure.infinitePi (fun _ : ℤ => ρ)) := by
-- proof
  apply StatMech.BeffaraDC.integrable_coord hρ i

/--
[integrable_animalValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean)
-/
@[path]
private lemma integrable_animalValue_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ]
  {n : ℕ}
-- given
  (hρ : Integrable (id : ℝ → ℝ) ρ) :
-- imply
  Integrable (fun ω : ℤ → ℝ => animalValue ω n) (Measure.infinitePi (fun _ : ℤ => ρ)) := by
-- proof
  apply StatMech.BeffaraDC.integrable_animalValue hρ n

/--
[animalCocycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean)
-/
@[path]
private lemma animalCocycle_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ]
-- given
  (hρ : Integrable (id : ℝ → ℝ) ρ) :
-- imply
  SubadditiveCocycle shiftEnv (Measure.infinitePi (fun _ : ℤ => ρ)) (fun n ω => animalValue ω n) where measurePreserving := by
-- proof
  apply StatMech.BeffaraDC.animalCocycle hρ

/--
[animalValue_nonneg_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean)
-/
@[path]
private lemma animalValue_nonneg_ae_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ]
  {n : ℕ} :
-- imply
  0 ≤ᵐ[Measure.infinitePi (fun _ : ℤ => ρ)] (fun ω => animalValue ω n) := by
-- proof
  apply StatMech.BeffaraDC.animalValue_nonneg_ae n

/--
[animalValue_lln_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean)
-/
@[path]
private lemma animalValue_lln_ae_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ]
-- given
  (hρ : Integrable (id : ℝ → ℝ) ρ) :
-- imply
  ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ)), Tendsto (fun n => animalValue ω n / n) atTop (𝓝 (kingmanLimit shiftEnv (fun n ω => animalValue ω n) ω)) := by
-- proof
  apply StatMech.BeffaraDC.animalValue_lln_ae hρ

/--
[animalLimit_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean)
-/
@[path]
private lemma animalLimit_integrable_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ]
-- given
  (hρ : Integrable (id : ℝ → ℝ) ρ) :
-- imply
  Integrable (animalLimit ρ) (Measure.infinitePi (fun _ : ℤ => ρ)) := by
-- proof
  apply StatMech.BeffaraDC.animalLimit_integrable hρ

/--
[animalLimit_nonneg_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean)
-/
@[path]
private lemma animalLimit_nonneg_ae_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ] :
-- imply
  0 ≤ᵐ[Measure.infinitePi (fun _ : ℤ => ρ)] animalLimit ρ := by
-- proof
  apply StatMech.BeffaraDC.animalLimit_nonneg_ae

/--
[animalLimit_shift_invariant_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean)
-/
@[path]
private lemma animalLimit_shift_invariant_ae_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ]
-- given
  (hρ : Integrable (id : ℝ → ℝ) ρ) :
-- imply
  ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ)), animalLimit ρ (shiftEnv ω) = animalLimit ρ ω := by
-- proof
  apply StatMech.BeffaraDC.animalLimit_shift_invariant_ae hρ

/--
[integral_animalLimit_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean)
-/
@[path]
private lemma integral_animalLimit_le_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ]
-- given
  (hρ : Integrable (id : ℝ → ℝ) ρ) :
-- imply
  (∫ ω, animalLimit ρ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ))) ≤ SubadditiveCocycle.gamma (animalCocycle hρ) := by
-- proof
  apply StatMech.BeffaraDC.integral_animalLimit_le hρ

/--
[integral_animalLimit_eq_gamma](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean)
-/
@[path]
private lemma integral_animalLimit_eq_gamma_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ]
-- given
  (hρ : Integrable (id : ℝ → ℝ) ρ) :
-- imply
  (∫ ω, animalLimit ρ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ))) = SubadditiveCocycle.gamma (animalCocycle hρ) := by
-- proof
  apply StatMech.BeffaraDC.integral_animalLimit_eq_gamma hρ

/--
[animalValue_eq_directed_window](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean)
-/
@[path]
private lemma animalValue_eq_directed_window_eq
  {ρ : Measure ℝ}
  {ω : ℤ → ℝ}
  {n : ℕ} :
-- imply
  animalValue ω n = (range (n + 1)).sup' (by simp) (fun a => ∑ i ∈ range a, ω (i : ℤ)) := by
-- proof
  apply StatMech.BeffaraDC.animalValue_eq_directed_window ω n


-- created on 2026-10-23
