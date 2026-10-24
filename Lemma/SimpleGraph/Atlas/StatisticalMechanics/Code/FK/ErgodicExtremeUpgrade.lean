import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.ErgodicExtremeUpgrade
open MeasureTheory Measure Set Filter StatMech StatMech.ConfigSpace StatMech.FK


/--
[aeconst_of_ae_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ErgodicExtremeUpgrade.lean)
-/
@[path]
private lemma aeconst_of_ae_invariant_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [Countable G]
  {s : Set (ConfigSpace E)}
-- given
  (hμ : IsErgodic (G := G) μ)
  (hs : MeasurableSet s)
  (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s =ᵐ[μ] s) :
-- imply
  μ s = 0 ∨ μ s = 1 := by
-- proof
  apply StatMech.ConfigSpace.aeconst_of_ae_invariant hμ hs hinv

/--
[ae_eq_const_of_ae_invariant_function](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ErgodicExtremeUpgrade.lean)
-/
@[path]
private lemma ae_eq_const_of_ae_invariant_function_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [Countable G]
  {φ : ConfigSpace E → ℝ≥0∞}
-- given
  (hμ : IsErgodic (G := G) μ)
  (hφ : Measurable φ)
  (hinv : ∀ g : G, φ ∘ (shift g : ConfigSpace E → ConfigSpace E) =ᵐ[μ] φ) :
-- imply
  ∃ c : ℝ≥0∞, φ =ᵐ[μ] Function.const _ c := by
-- proof
  apply StatMech.ConfigSpace.ae_eq_const_of_ae_invariant_function hμ hφ hinv

/--
[eq_smul_of_absolutelyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ErgodicExtremeUpgrade.lean)
-/
@[path]
private lemma eq_smul_of_absolutelyContinuous_eq
  [Group G]
  [MulAction G E]
  {μ ν : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [IsFiniteMeasure ν]
  [Countable G]
-- given
  (hμ : IsErgodic (G := G) μ)
  (hν : IsTranslationInvariant (G := G) ν)
  (hνμ : ν ≪ μ) :
-- imply
  ∃ c : ℝ≥0∞, ν = c • μ := by
-- proof
  apply StatMech.ConfigSpace.eq_smul_of_absolutelyContinuous hμ hν hνμ

/--
[eeu_ergodic_summand_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ErgodicExtremeUpgrade.lean)
-/
@[path]
private lemma eeu_ergodic_summand_eq_eq
  [Group G]
  [MulAction G E]
  {μ ν₁ ν₂ : Measure (ConfigSpace E)}
  {a b : ℝ≥0∞}
  [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν₁]
  [Countable G]
-- given
  (hμ : IsErgodic (G := G) μ)
  (hν₁ : IsTranslationInvariant (G := G) ν₁)
  (hconv : μ = a • ν₁ + b • ν₂)
  (ha : 0 < a) :
-- imply
  ν₁ = μ := by
-- proof
  apply StatMech.ConfigSpace.eeu_ergodic_summand_eq hμ hν₁ hconv ha

/--
[eeu_ergodic_summands_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ErgodicExtremeUpgrade.lean)
-/
@[path]
private lemma eeu_ergodic_summands_eq_eq
  [Group G]
  [MulAction G E]
  {μ ν₁ ν₂ : Measure (ConfigSpace E)}
  {a b : ℝ≥0∞}
  [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν₁]
  [IsProbabilityMeasure ν₂]
  [Countable G]
-- given
  (hμ : IsErgodic (G := G) μ)
  (hν₁ : IsTranslationInvariant (G := G) ν₁)
  (hν₂ : IsTranslationInvariant (G := G) ν₂)
  (hconv : μ = a • ν₁ + b • ν₂)
  (ha : 0 < a)
  (hb : 0 < b) :
-- imply
  ν₁ = μ ∧ ν₂ = μ := by
-- proof
  apply StatMech.ConfigSpace.eeu_ergodic_summands_eq hμ hν₁ hν₂ hconv ha hb

/--
[eeu_isInvariantExtremePoint_of_ergodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ErgodicExtremeUpgrade.lean)
-/
@[path]
private lemma eeu_isInvariantExtremePoint_of_ergodic_eq
  [Group G]
  [MulAction G E]
  [Countable G]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
-- given
  (hμ : IsErgodic (G := G) μ) :
-- imply
  IsInvariantExtremePoint (G := G) μ := by
-- proof
  apply StatMech.FK.eeu_isInvariantExtremePoint_of_ergodic hμ

/--
[eeu_wiredIV_isInvariantExtremePoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ErgodicExtremeUpgrade.lean)
-/
@[path]
private lemma eeu_wiredIV_isInvariantExtremePoint_eq
  [Group G]
  [MulAction G E]
  {d : ℕ}
  {p : ℝ}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  IsInvariantExtremePoint (G := Multiplicative (Lattice.Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))) := by
-- proof
  apply StatMech.FK.eeu_wiredIV_isInvariantExtremePoint hd hp hp1

/--
[eeu_wiredIV_extremePoint_clause](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ErgodicExtremeUpgrade.lean)
-/
@[path]
private lemma eeu_wiredIV_extremePoint_clause_eq
  [Group G]
  [MulAction G E]
  {d : ℕ}
  {p : ℝ}
  {ν₁ ν₂ : Measure (ConfigSpace (Sym2 (Lattice.Site d)))}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (a b : ℝ≥0∞)
  (h0 : IsTranslationInvariant (G := Multiplicative (Lattice.Site d)) ν₁)
  (h1 : IsTranslationInvariant (G := Multiplicative (Lattice.Site d)) ν₂)
  (hp1' : IsProbabilityMeasure ν₁)
  (hp2' : IsProbabilityMeasure ν₂)
  (ha : 0 < a)
  (hb : 0 < b)
  (hab : a + b = 1)
  (hconv : (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))) = a • ν₁ + b • ν₂) :
-- imply
  ν₁ = ν₂ := by
-- proof
  apply StatMech.FK.eeu_wiredIV_extremePoint_clause hd hp hp1 ν₁ ν₂ a b h0 h1 hp1' hp2' ha hb hab hconv


-- created on 2026-10-23
