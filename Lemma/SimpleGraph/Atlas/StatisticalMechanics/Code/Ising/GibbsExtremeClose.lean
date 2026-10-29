import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtremeClose
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology StatMech StatMech.Ising


/--
[gec_convexSummand_eq_on_clopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtremeClose.lean)
-/
@[path]
private lemma gec_convexSummand_eq_on_clopen_eq
  {d : ℕ}
  {μ ν₁ ν₂ : Measure (ConfigSpace E)}
  {a b : ENNReal}
  [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν₁]
  [IsProbabilityMeasure ν₂]
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hab : a + b = 1)
  (hat : a ≠ ⊤)
  (hbt : b ≠ ⊤)
  (hconv : μ = a • ν₁ + b • ν₂)
  (h0 : ν₁ ≼c μ)
  (h1 : ν₂ ≼c μ) :
-- imply
  μ ≼c ν₁ := by
-- proof
  apply StatMech.Ising.gec_convexSummand_eq_on_clopen ha hb hab hat hbt hconv h0 h1

/--
[gec_max_extreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtremeClose.lean)
-/
@[path]
private lemma gec_max_extreme_eq
  {d : ℕ}
  [Countable E]
  {μ ν₁ ν₂ : Measure (ConfigSpace E)}
  {a b : ENNReal}
  [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν₁]
  [IsProbabilityMeasure ν₂]
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hab : a + b = 1)
  (hat : a ≠ ⊤)
  (hbt : b ≠ ⊤)
  (hconv : μ = a • ν₁ + b • ν₂)
  (h0 : ν₁ ≼c μ)
  (h1 : ν₂ ≼c μ) :
-- imply
  ν₁ = μ ∧ ν₂ = μ := by
-- proof
  apply StatMech.Ising.gec_max_extreme ha hb hab hat hbt hconv h0 h1

/--
[gec_min_extreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtremeClose.lean)
-/
@[path]
private lemma gec_min_extreme_eq
  {d : ℕ}
  [Countable E]
  {μ ν₁ ν₂ : Measure (ConfigSpace E)}
  {a b : ENNReal}
  [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν₁]
  [IsProbabilityMeasure ν₂]
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hab : a + b = 1)
  (hat : a ≠ ⊤)
  (hbt : b ≠ ⊤)
  (hconv : μ = a • ν₁ + b • ν₂)
  (h0 : μ ≼c ν₁)
  (h1 : μ ≼c ν₂) :
-- imply
  ν₁ = μ ∧ ν₂ = μ := by
-- proof
  apply StatMech.Ising.gec_min_extreme ha hb hab hat hbt hconv h0 h1

/--
[gec_plusState_extreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtremeClose.lean)
-/
@[path]
private lemma gec_plusState_extreme_eq
  {d : ℕ}
  {ν₁ ν₂ : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure ν₁]
  [IsProbabilityMeasure ν₂]
  {a b : ENNReal}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (h₁ : IsDLRState d β h ν₁)
  (h₂ : IsDLRState d β h ν₂)
  (ha : 0 < a)
  (hb : 0 < b)
  (hab : a + b = 1)
  (hat : a ≠ ⊤)
  (hbt : b ≠ ⊤)
  (hconv : (plusState d β h : Measure (ConfigSpace (Site d))) = a • ν₁ + b • ν₂) :
-- imply
  ν₁ = (plusState d β h : Measure (ConfigSpace (Site d))) ∧ ν₂ = (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.gec_plusState_extreme β h hβ hh h₁ h₂ ha hb hab hat hbt hconv

/--
[gec_minusState_extreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtremeClose.lean)
-/
@[path]
private lemma gec_minusState_extreme_eq
  {d : ℕ}
  {ν₁ ν₂ : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure ν₁]
  [IsProbabilityMeasure ν₂]
  {a b : ENNReal}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (h₁ : IsDLRState d β h ν₁)
  (h₂ : IsDLRState d β h ν₂)
  (ha : 0 < a)
  (hb : 0 < b)
  (hab : a + b = 1)
  (hat : a ≠ ⊤)
  (hbt : b ≠ ⊤)
  (hconv : (minusState d β h : Measure (ConfigSpace (Site d))) = a • ν₁ + b • ν₂) :
-- imply
  ν₁ = (minusState d β h : Measure (ConfigSpace (Site d))) ∧ ν₂ = (minusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.gec_minusState_extreme β h hβ hh h₁ h₂ ha hb hab hat hbt hconv

/--
[gec_plusState_no_proper_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtremeClose.lean)
-/
@[path]
private lemma gec_plusState_no_proper_split_eq
  {d : ℕ}
  {ν₁ ν₂ : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure ν₁]
  [IsProbabilityMeasure ν₂]
  {a b : ENNReal}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (h₁ : IsDLRState d β h ν₁)
  (h₂ : IsDLRState d β h ν₂)
  (ha : 0 < a)
  (hb : 0 < b)
  (hab : a + b = 1)
  (hat : a ≠ ⊤)
  (hbt : b ≠ ⊤)
  (hconv : (plusState d β h : Measure (ConfigSpace (Site d))) = a • ν₁ + b • ν₂) :
-- imply
  ν₁ = ν₂ := by
-- proof
  apply StatMech.Ising.gec_plusState_no_proper_split β h hβ hh h₁ h₂ ha hb hab hat hbt hconv

/--
[gec_minusState_no_proper_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtremeClose.lean)
-/
@[path]
private lemma gec_minusState_no_proper_split_eq
  {d : ℕ}
  {ν₁ ν₂ : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure ν₁]
  [IsProbabilityMeasure ν₂]
  {a b : ENNReal}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (h₁ : IsDLRState d β h ν₁)
  (h₂ : IsDLRState d β h ν₂)
  (ha : 0 < a)
  (hb : 0 < b)
  (hab : a + b = 1)
  (hat : a ≠ ⊤)
  (hbt : b ≠ ⊤)
  (hconv : (minusState d β h : Measure (ConfigSpace (Site d))) = a • ν₁ + b • ν₂) :
-- imply
  ν₁ = ν₂ := by
-- proof
  apply StatMech.Ising.gec_minusState_no_proper_split β h hβ hh h₁ h₂ ha hb hab hat hbt hconv

/--
[gec_cond_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtremeClose.lean)
-/
@[path]
private lemma gec_cond_isTranslationInvariant_eq
  {d : ℕ}
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
  apply StatMech.Ising.gec_cond_isTranslationInvariant hμ hs hinv

/--
[gec_invariant_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtremeClose.lean)
-/
@[path]
private lemma gec_invariant_decomp_eq
  {d : ℕ}
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
  apply StatMech.Ising.gec_invariant_decomp hs hs0 hsc0

/--
[gec_ergodic_of_noProperSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtremeClose.lean)
-/
@[path]
private lemma gec_ergodic_of_noProperSplit_eq
  {d : ℕ}
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
-- given
  (hti : IsTranslationInvariant (G := G) μ)
  (P : Measure (ConfigSpace E) → Prop)
  (hsplit : ∀ (ν₁ ν₂ : Measure (ConfigSpace E)) (a b : ENNReal), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ → P ν₁ → P ν₂ → 0 < a → 0 < b → a + b = 1 → a ≠ ⊤ → b ≠ ⊤ → μ = a • ν₁ + b • ν₂ → ν₁ = ν₂)
  (hclosure : ∀ {s : Set (ConfigSpace E)}, MeasurableSet s → (∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) → μ s ≠ 0 → μ sᶜ ≠ 0 → P (μ[|s]) ∧ P (μ[|sᶜ])) :
-- imply
  IsErgodic (G := G) μ := by
-- proof
  apply StatMech.Ising.gec_ergodic_of_noProperSplit hti P hsplit hclosure

/--
[gec_plusState_isErgodic_of_closure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtremeClose.lean)
-/
@[path]
private lemma gec_plusState_isErgodic_of_closure_eq
  {d : ℕ}
  [Group G]
  [MulAction G E]
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hti : IsTranslationInvariant (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))))
  (hclosure : ∀ {s : Set (ConfigSpace (Site d))}, MeasurableSet s → (∀ g : Multiplicative (Site d), (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' s = s) → (plusState d β h : Measure (ConfigSpace (Site d))) s ≠ 0 → (plusState d β h : Measure (ConfigSpace (Site d))) sᶜ ≠ 0 → IsDLRState d β h ((plusState d β h : Measure (ConfigSpace (Site d)))[|s]) ∧ IsDLRState d β h ((plusState d β h : Measure (ConfigSpace (Site d)))[|sᶜ])) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.gec_plusState_isErgodic_of_closure β h hβ hh hti hclosure

/--
[gec_minusState_isErgodic_of_closure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsExtremeClose.lean)
-/
@[path]
private lemma gec_minusState_isErgodic_of_closure_eq
  {d : ℕ}
  [Group G]
  [MulAction G E]
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hti : IsTranslationInvariant (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d))))
  (hclosure : ∀ {s : Set (ConfigSpace (Site d))}, MeasurableSet s → (∀ g : Multiplicative (Site d), (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' s = s) → (minusState d β h : Measure (ConfigSpace (Site d))) s ≠ 0 → (minusState d β h : Measure (ConfigSpace (Site d))) sᶜ ≠ 0 → IsDLRState d β h ((minusState d β h : Measure (ConfigSpace (Site d)))[|s]) ∧ IsDLRState d β h ((minusState d β h : Measure (ConfigSpace (Site d)))[|sᶜ])) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.gec_minusState_isErgodic_of_closure β h hβ hh hti hclosure


-- created on 2026-10-23
