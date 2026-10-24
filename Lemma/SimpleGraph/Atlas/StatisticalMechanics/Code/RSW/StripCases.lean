import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.RSW.StripCases
open Set MeasureTheory StatMech StatMech.RSW StatMech.RSW.StripCases


/--
[rsc_pigeonhole_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/StripCases.lean)
-/
@[path]
private lemma rsc_pigeonhole_cover_eq
  [MeasurableSpace E]
  {μ : Measure E}
  [IsProbabilityMeasure μ]
  {t : Finset ι}
  {A : ι → Set E}
  {Ev : Set E}
  {s : ℝ}
-- given
  (hEv : s ≤ μ.real Ev)
  (hcover : Ev ⊆ ⋃ i ∈ t, A i)
  (htne : t.Nonempty) :
-- imply
  ∃ i ∈ t, s / (t.card : ℝ) ≤ μ.real (A i) := by
-- proof
  apply StatMech.RSW.StripCases.rsc_pigeonhole_cover μ t A hEv hcover htne

/--
[rsc_strip_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/StripCases.lean)
-/
@[path]
private lemma rsc_strip_dichotomy_eq
  [MeasurableSpace E]
  {μ : Measure E}
  [IsProbabilityMeasure μ]
  {k : ℕ}
  {H V : Set E}
  {A : ℕ → Set E}
-- given
  (hk : 1 ≤ k)
  (hcompl : μ.real H < 1 / 2 → 1 / 2 ≤ μ.real V)
  (hcover : V ⊆ ⋃ i ∈ Finset.range (18 * k), A i) :
-- imply
  (1 / 2 ≤ μ.real H) ∨ (∃ i ∈ Finset.range (18 * k), (1 : ℝ) / (36 * k) ≤ μ.real (A i)) := by
-- proof
  apply StatMech.RSW.StripCases.rsc_strip_dichotomy μ hk H V A hcompl hcover

/--
[rsc_three_way](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/StripCases.lean)
-/
@[path]
private lemma rsc_three_way_eq
  {a b c' c₁ : ℝ}
-- given
  (hub : c₁ ≤ a + b + c')
  (hsym : b = c') :
-- imply
  c₁ / 3 ≤ a ∨ c₁ / 3 ≤ b := by
-- proof
  apply StatMech.RSW.StripCases.rsc_three_way hub hsym

/--
[rsc_strip_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/StripCases.lean)
-/
@[path]
private lemma rsc_strip_cases_eq
  [MeasurableSpace E]
  {μ : Measure E}
  [IsProbabilityMeasure μ]
  {c₁ : ℝ}
  {Arm Top Left Right : Set E}
-- given
  (hArm : c₁ ≤ μ.real Arm)
  (hcover : Arm ⊆ Top ∪ Left ∪ Right)
  (hsym : μ.real Left = μ.real Right) :
-- imply
  (c₁ / 3 ≤ μ.real Top) ∨ (c₁ / 3 ≤ μ.real Left) := by
-- proof
  apply StatMech.RSW.StripCases.rsc_strip_cases μ Arm Top Left Right hArm hcover hsym

/--
[rsc_dichotomy_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/StripCases.lean)
-/
@[path]
private lemma rsc_dichotomy_cases_eq
  [MeasurableSpace E]
  {μ : Measure E}
  [IsProbabilityMeasure μ]
  {k : ℕ}
  {H V : Set E}
  {A Top Left Right : ℕ → Set E}
-- given
  (hk : 1 ≤ k)
  (hH : μ.real H < 1 / 2)
  (hcompl : μ.real H < 1 / 2 → 1 / 2 ≤ μ.real V)
  (hcover : V ⊆ ⋃ i ∈ Finset.range (18 * k), A i)
  (hcase : ∀ i, A i ⊆ Top i ∪ Left i ∪ Right i)
  (hsym : ∀ i, μ.real (Left i) = μ.real (Right i)) :
-- imply
  ∃ i ∈ Finset.range (18 * k), ((1 : ℝ) / (108 * k) ≤ μ.real (Top i)) ∨ ((1 : ℝ) / (108 * k) ≤ μ.real (Left i)) := by
-- proof
  apply StatMech.RSW.StripCases.rsc_dichotomy_cases μ hk H V A Top Left Right hH hcompl hcover hcase hsym


-- created on 2026-10-23
