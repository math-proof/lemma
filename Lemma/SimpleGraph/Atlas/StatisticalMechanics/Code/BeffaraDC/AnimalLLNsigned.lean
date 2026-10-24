import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.AnimalLLNsigned
open MeasureTheory Filter Topology Finset StatMech.Kingman StatMech.KingmanAE StatMech.KingmanFilling StatMech.KingmanSigned StatMech StatMech.BeffaraDC


/--
[signedAnimalValue_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNsigned.lean)
-/
@[path]
private lemma signedAnimalValue_zero_eq
  {ρ : Measure ℝ}
  {ω : ℤ → ℝ}
  {c : ℝ} :
-- imply
  signedAnimalValue ω c 0 = 0 := by
-- proof
  apply StatMech.BeffaraDC.signedAnimalValue_zero ω c

/--
[signedAnimalValue_subadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNsigned.lean)
-/
@[path]
private lemma signedAnimalValue_subadditive_eq
  {ρ : Measure ℝ}
  {ω : ℤ → ℝ}
  {c : ℝ}
  {m n : ℕ} :
-- imply
  signedAnimalValue ω c (m + n) ≤ signedAnimalValue ω c m + signedAnimalValue (shiftEnv^[m] ω) c n := by
-- proof
  apply StatMech.BeffaraDC.signedAnimalValue_subadditive ω c m n

/--
[measurable_signedAnimalValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNsigned.lean)
-/
@[path]
private lemma measurable_signedAnimalValue_eq
  {ρ : Measure ℝ}
  {c : ℝ}
  {n : ℕ} :
-- imply
  Measurable (fun ω : ℤ → ℝ => signedAnimalValue ω c n) := by
-- proof
  apply StatMech.BeffaraDC.measurable_signedAnimalValue c n

/--
[integrable_signedAnimalValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNsigned.lean)
-/
@[path]
private lemma integrable_signedAnimalValue_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ]
  {c : ℝ}
  {n : ℕ}
-- given
  (hρ : Integrable (id : ℝ → ℝ) ρ) :
-- imply
  Integrable (fun ω : ℤ → ℝ => signedAnimalValue ω c n) (Measure.infinitePi (fun _ : ℤ => ρ)) := by
-- proof
  apply StatMech.BeffaraDC.integrable_signedAnimalValue hρ c n

/--
[signedAnimalCocycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNsigned.lean)
-/
@[path]
private lemma signedAnimalCocycle_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ]
  {c : ℝ}
-- given
  (hρ : Integrable (id : ℝ → ℝ) ρ) :
-- imply
  SubadditiveCocycle shiftEnv (Measure.infinitePi (fun _ : ℤ => ρ)) (fun n ω => signedAnimalValue ω c n) where measurePreserving := by
-- proof
  apply StatMech.BeffaraDC.signedAnimalCocycle hρ c

/--
[expSeq_signedAnimalValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNsigned.lean)
-/
@[path]
private lemma expSeq_signedAnimalValue_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ]
  {c : ℝ}
  {n : ℕ}
-- given
  (hρ : Integrable (id : ℝ → ℝ) ρ) :
-- imply
  SubadditiveCocycle.expSeq (fun n ω => signedAnimalValue ω c n) (Measure.infinitePi (fun _ : ℤ => ρ)) n = SubadditiveCocycle.expSeq (fun n ω => animalValue ω n) (Measure.infinitePi (fun _ : ℤ => ρ)) n - c * n := by
-- proof
  apply StatMech.BeffaraDC.expSeq_signedAnimalValue hρ c n

/--
[bddBelow_expSeq_signedAnimalValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNsigned.lean)
-/
@[path]
private lemma bddBelow_expSeq_signedAnimalValue_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ]
  {c : ℝ}
-- given
  (hρ : Integrable (id : ℝ → ℝ) ρ) :
-- imply
  BddBelow (Set.range fun n => SubadditiveCocycle.expSeq (fun n ω => signedAnimalValue ω c n) (Measure.infinitePi (fun _ : ℤ => ρ)) n / n) := by
-- proof
  apply StatMech.BeffaraDC.bddBelow_expSeq_signedAnimalValue hρ c

/--
[signedAnimalValue_lln_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNsigned.lean)
-/
@[path]
private lemma signedAnimalValue_lln_ae_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ]
  {c : ℝ}
-- given
  (hρ : Integrable (id : ℝ → ℝ) ρ) :
-- imply
  ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ)), Tendsto (fun n => signedAnimalValue ω c n / n) atTop (𝓝 (kingmanLimit shiftEnv (fun n ω => signedAnimalValue ω c n) ω)) := by
-- proof
  apply StatMech.BeffaraDC.signedAnimalValue_lln_ae hρ c

/--
[signedAnimalValue_div_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNsigned.lean)
-/
@[path]
private lemma signedAnimalValue_div_eq_eq
  {ρ : Measure ℝ}
  {ω : ℤ → ℝ}
  {c : ℝ}
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  signedAnimalValue ω c n / n = animalValue ω n / n - c := by
-- proof
  apply StatMech.BeffaraDC.signedAnimalValue_div_eq ω c hn

/--
[tendsto_signedAnimalValue_div_animalLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNsigned.lean)
-/
@[path]
private lemma tendsto_signedAnimalValue_div_animalLimit_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ]
  {c : ℝ}
-- given
  (hρ : Integrable (id : ℝ → ℝ) ρ) :
-- imply
  ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ)), Tendsto (fun n => signedAnimalValue ω c n / n) atTop (𝓝 (animalLimit ρ ω - c)) := by
-- proof
  apply StatMech.BeffaraDC.tendsto_signedAnimalValue_div_animalLimit hρ c

/--
[signedAnimalLimit_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNsigned.lean)
-/
@[path]
private lemma signedAnimalLimit_eq_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ]
  {c : ℝ}
-- given
  (hρ : Integrable (id : ℝ → ℝ) ρ) :
-- imply
  ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ)), kingmanLimit shiftEnv (fun n ω => signedAnimalValue ω c n) ω = animalLimit ρ ω - c := by
-- proof
  apply StatMech.BeffaraDC.signedAnimalLimit_eq hρ c

/--
[animalValue_lln_ae_via_signed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNsigned.lean)
-/
@[path]
private lemma animalValue_lln_ae_via_signed_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ]
-- given
  (hρ : Integrable (id : ℝ → ℝ) ρ) :
-- imply
  ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ)), Tendsto (fun n => animalValue ω n / n) atTop (𝓝 (animalLimit ρ ω)) := by
-- proof
  apply StatMech.BeffaraDC.animalValue_lln_ae_via_signed hρ

/--
[signedAnimalValue_eventually_pos_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNsigned.lean)
-/
@[path]
private lemma signedAnimalValue_eventually_pos_ae_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ]
  {c : ℝ}
-- given
  (hρ : Integrable (id : ℝ → ℝ) ρ) :
-- imply
  ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ)), c < animalLimit ρ ω → ∀ᶠ n in atTop, 0 < signedAnimalValue ω c n := by
-- proof
  apply StatMech.BeffaraDC.signedAnimalValue_eventually_pos_ae hρ c

/--
[signedAnimalValue_eventually_neg_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNsigned.lean)
-/
@[path]
private lemma signedAnimalValue_eventually_neg_ae_eq
  {ρ : Measure ℝ}
  [IsProbabilityMeasure ρ]
  {c : ℝ}
-- given
  (hρ : Integrable (id : ℝ → ℝ) ρ) :
-- imply
  ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ)), animalLimit ρ ω < c → ∀ᶠ n in atTop, signedAnimalValue ω c n < 0 := by
-- proof
  apply StatMech.BeffaraDC.signedAnimalValue_eventually_neg_ae hρ c


-- created on 2026-10-23
