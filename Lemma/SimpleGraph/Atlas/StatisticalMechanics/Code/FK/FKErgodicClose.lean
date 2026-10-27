import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.FKErgodicClose.Part2
open MeasureTheory ProbabilityTheory Filter Topology StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[fec_restrict_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKErgodicClose.lean)
-/
@[path]
private lemma fec_restrict_measurePreserving_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  {g : G}
  {s : Set (ConfigSpace E)}
-- given
  (hμ : IsTranslationInvariant (G := G) μ)
  (hs : MeasurableSet s)
  (hinv : (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
-- imply
  MeasurePreserving (shift g : ConfigSpace E → ConfigSpace E) (μ.restrict s) (μ.restrict s) := by
-- proof
  apply StatMech.FK.fec_restrict_measurePreserving hμ g hs hinv

/--
[fec_cond_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKErgodicClose.lean)
-/
@[path]
private lemma fec_cond_isTranslationInvariant_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  {s : Set (ConfigSpace E)}
-- given
  (hμ : IsTranslationInvariant (G := G) μ)
  (hs : MeasurableSet s)
  (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
-- imply
  IsTranslationInvariant (G := G) (μ[|s]) := by
-- proof
  apply StatMech.FK.fec_cond_isTranslationInvariant hμ hs hinv

/--
[fec_invariant_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKErgodicClose.lean)
-/
@[path]
private lemma fec_invariant_decomp_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsFiniteMeasure μ]
  {s : Set (ConfigSpace E)}
-- given
  (hs : MeasurableSet s)
  (hs0 : μ s ≠ 0)
  (hsc0 : μ sᶜ ≠ 0) :
-- imply
  μ = (μ s) • (μ[|s]) + (μ sᶜ) • (μ[|sᶜ]) := by
-- proof
  apply StatMech.FK.fec_invariant_decomp hs hs0 hsc0

/--
[fec_isErgodic_of_invariantExtremePoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKErgodicClose.lean)
-/
@[path]
private lemma fec_isErgodic_of_invariantExtremePoint_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
-- given
  (hμ : IsInvariantExtremePoint (G := G) μ) :
-- imply
  IsErgodic (G := G) μ := by
-- proof
  apply StatMech.FK.fec_isErgodic_of_invariantExtremePoint hμ

/--
[fec_wiredIV_isErgodic_of_extremePoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKErgodicClose.lean)
-/
@[path]
private lemma fec_wiredIV_isErgodic_of_extremePoint_eq
  [Group G]
  [MulAction G E]
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hext : ∀ (ν₁ ν₂ : Measure (ConfigSpace (Sym2 (Site d)))) (a b : ℝ≥0∞), IsTranslationInvariant (G := Multiplicative (Site d)) ν₁ → IsTranslationInvariant (G := Multiplicative (Site d)) ν₂ → IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ → 0 < a → 0 < b → a + b = 1 → (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) = a • ν₁ + b • ν₂ → ν₁ = ν₂) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fec_wiredIV_isErgodic_of_extremePoint hp hp1 hext

/--
[fec_freeIV_isErgodic_of_extremePoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKErgodicClose.lean)
-/
@[path]
private lemma fec_freeIV_isErgodic_of_extremePoint_eq
  [Group G]
  [MulAction G E]
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (htifree : IsTranslationInvariant (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))))
  (hext : ∀ (ν₁ ν₂ : Measure (ConfigSpace (Sym2 (Site d)))) (a b : ℝ≥0∞), IsTranslationInvariant (G := Multiplicative (Site d)) ν₁ → IsTranslationInvariant (G := Multiplicative (Site d)) ν₂ → IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ → 0 < a → 0 < b → a + b = 1 → (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) = a • ν₁ + b • ν₂ → ν₁ = ν₂) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fec_freeIV_isErgodic_of_extremePoint hp hp1 htifree hext


-- created on 2026-10-23
