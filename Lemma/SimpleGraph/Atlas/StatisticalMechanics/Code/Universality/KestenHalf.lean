import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.KestenHalf
open MeasureTheory Set Filter Topology StatMech StatMech.Universality


/--
[halfMeasure_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenHalf.lean)
-/
@[path]
private lemma halfMeasure_eq_eq :
-- imply
  halfMeasure = bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one := by
-- proof
  apply StatMech.Universality.halfMeasure_eq

/--
[measurable_dualConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenHalf.lean)
-/
@[path]
private lemma measurable_dualConfig_eq :
-- imply
  Measurable (dualConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.measurable_dualConfig

/--
[dualConfig_preserves_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenHalf.lean)
-/
@[path]
private lemma dualConfig_preserves_half_eq :
-- imply
  Measure.map dualConfig halfMeasure = halfMeasure := by
-- proof
  apply StatMech.Universality.dualConfig_preserves_half

/--
[selfDualRotation_preserves_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenHalf.lean)
-/
@[path]
private lemma selfDualRotation_preserves_half_eq
  {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
-- given
  (hRmeas : Measurable R)
  (hRpres : Measure.map R halfMeasure = halfMeasure) :
-- imply
  Measure.map (R ∘ dualConfig) halfMeasure = halfMeasure := by
-- proof
  apply StatMech.Universality.selfDualRotation_preserves_half R hRmeas hRpres

/--
[half_crossingProb_of_selfDual_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenHalf.lean)
-/
@[path]
private lemma half_crossingProb_of_selfDual_dichotomy_eq
  {H : Set (ConfigSpace (Sym2 (Site 2)))}
  {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
-- given
  (hHm : MeasurableSet H)
  (hRmeas : Measurable R)
  (hRpres : Measure.map R halfMeasure = halfMeasure)
  (hdich : Hᶜ = (R ∘ dualConfig) ⁻¹' H) :
-- imply
  halfMeasure.real H = 1 / 2 := by
-- proof
  apply StatMech.Universality.half_crossingProb_of_selfDual_dichotomy hHm hRmeas hRpres hdich

/--
[percolationProbability_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenHalf.lean)
-/
@[path]
private lemma percolationProbability_congr_eq
  {d : ℕ}
  {p q : ℝ≥0}
-- given
  (hp : p ≤ 1)
  (hq : q ≤ 1)
  (h : p = q) :
-- imply
  percolationProbability d p hp = percolationProbability d q hq := by
-- proof
  apply StatMech.Universality.percolationProbability_congr hp hq h

/--
[subcriticalDensities_bddAbove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenHalf.lean)
-/
@[path]
private lemma subcriticalDensities_bddAbove_eq
  {d : ℕ} :
-- imply
  BddAbove (subcriticalDensities d) := by
-- proof
  apply StatMech.Universality.subcriticalDensities_bddAbove d

/--
[half_mem_subcriticalDensities](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenHalf.lean)
-/
@[path]
private lemma half_mem_subcriticalDensities_eq
-- given
  (h : percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0) :
-- imply
  ((1 : ℝ) / 2) ∈ subcriticalDensities 2 := by
-- proof
  apply StatMech.Universality.half_mem_subcriticalDensities h

/--
[half_le_criticalProbability_of_subcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenHalf.lean)
-/
@[path]
private lemma half_le_criticalProbability_of_subcritical_eq
-- given
  (h : percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0) :
-- imply
  (1 : ℝ) / 2 ≤ criticalProbability 2 := by
-- proof
  apply StatMech.Universality.half_le_criticalProbability_of_subcritical h

/--
[criticalProbability_le_half_of_sharpThreshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenHalf.lean)
-/
@[path]
private lemma criticalProbability_le_half_of_sharpThreshold_eq
  {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
-- given
  (hSharpThreshold : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 → Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0))
  (hbalance : ∀ n : ℕ, halfMeasure.real (boxFam n) = 1 / 2) :
-- imply
  criticalProbability 2 ≤ (1 : ℝ) / 2 := by
-- proof
  apply StatMech.Universality.criticalProbability_le_half_of_sharpThreshold hSharpThreshold hbalance

/--
[kesten_pc_eq_half_of_bxp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenHalf.lean)
-/
@[path]
private lemma kesten_pc_eq_half_of_bxp_eq
  {ρ : ℝ}
  {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
  {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
-- given
  (hbxp : BoxCrossingProperty halfMeasure ρ)
  (hCorLowerBound : BoxCrossingProperty halfMeasure ρ → percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0)
  (hHm : ∀ n, MeasurableSet (boxFam n))
  (hRmeas : Measurable R)
  (hRpres : Measure.map R halfMeasure = halfMeasure)
  (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n))
  (hSharpThreshold : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 → Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0)) :
-- imply
  criticalProbability 2 = 1 / 2 := by
-- proof
  apply StatMech.Universality.kesten_pc_eq_half_of_bxp hbxp hCorLowerBound hHm hRmeas hRpres hdich hSharpThreshold

/--
[kesten_no_percolation_at_pc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenHalf.lean)
-/
@[path]
private lemma kesten_no_percolation_at_pc_eq
  {ρ : ℝ}
  {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
  {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
-- given
  (hbxp : BoxCrossingProperty halfMeasure ρ)
  (hCorLowerBound : BoxCrossingProperty halfMeasure ρ → percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0)
  (hHm : ∀ n, MeasurableSet (boxFam n))
  (hRmeas : Measurable R)
  (hRpres : Measure.map R halfMeasure = halfMeasure)
  (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n))
  (hSharpThreshold : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 → Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0)) :
-- imply
  criticalProbability 2 = 1 / 2 ∧ percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 := by
-- proof
  apply StatMech.Universality.kesten_no_percolation_at_pc hbxp hCorLowerBound hHm hRmeas hRpres hdich hSharpThreshold


-- created on 2026-10-23
