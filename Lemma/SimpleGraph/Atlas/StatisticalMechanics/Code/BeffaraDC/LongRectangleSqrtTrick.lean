import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleSqrtTrick
open MeasureTheory Set StatMech StatMech.BeffaraDC


/--
[finite_complUnion_fkg_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleSqrtTrick.lean)
-/
@[path]
private lemma finite_complUnion_fkg_bound_eq
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {s : Finset ι}
  {A : ι → Set (ConfigSpace E)}
-- given
  (hpa : PositivelyAssociated μ)
  (hA : ∀ i ∈ s, IsIncreasing (A i))
  (hAm : ∀ i ∈ s, MeasurableSet (A i)) :
-- imply
  (∏ i ∈ s, (1 - μ.real (A i))) ≤ 1 - μ.real (⋃ i ∈ s, A i) := by
-- proof
  apply StatMech.BeffaraDC.finite_complUnion_fkg_bound μ hpa s A hA hAm

/--
[finite_symmetric_sqrt_trick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleSqrtTrick.lean)
-/
@[path]
private lemma finite_symmetric_sqrt_trick_eq
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {s : Finset ι}
  {A : ι → Set (ConfigSpace E)}
  {i₀ : ι}
-- given
  (hpa : PositivelyAssociated μ)
  (hi₀ : i₀ ∈ s)
  (hA : ∀ i ∈ s, IsIncreasing (A i))
  (hAm : ∀ i ∈ s, MeasurableSet (A i))
  (hsym : ∀ i ∈ s, μ.real (A i) = μ.real (A i₀)) :
-- imply
  1 - (1 - μ.real (⋃ i ∈ s, A i)) ^ ((1 : ℝ) / s.card) ≤ μ.real (A i₀) := by
-- proof
  apply StatMech.BeffaraDC.finite_symmetric_sqrt_trick μ hpa s A hi₀ hA hAm hsym

/--
[finite_symmetric_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleSqrtTrick.lean)
-/
@[path]
private lemma finite_symmetric_deficit_eq
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {s : Finset ι}
  {A : ι → Set (ConfigSpace E)}
  {i₀ : ι}
  {δ : ℝ}
-- given
  (hpa : PositivelyAssociated μ)
  (hi₀ : i₀ ∈ s)
  (hA : ∀ i ∈ s, IsIncreasing (A i))
  (hAm : ∀ i ∈ s, MeasurableSet (A i))
  (hsym : ∀ i ∈ s, μ.real (A i) = μ.real (A i₀))
  (hunion : 1 - μ.real (⋃ i ∈ s, A i) ≤ δ) :
-- imply
  1 - δ ^ ((1 : ℝ) / s.card) ≤ μ.real (A i₀) := by
-- proof
  apply StatMech.BeffaraDC.finite_symmetric_deficit μ hpa s A hi₀ hA hAm hsym hunion

/--
[finite_symmetric_polynomial_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleSqrtTrick.lean)
-/
@[path]
private lemma finite_symmetric_polynomial_deficit_eq
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {s : Finset ι}
  {A : ι → Set (ConfigSpace E)}
  {i₀ : ι}
  {c ε : ℝ}
  {n : ℕ}
-- given
  (hpa : PositivelyAssociated μ)
  (hi₀ : i₀ ∈ s)
  (hA : ∀ i ∈ s, IsIncreasing (A i))
  (hAm : ∀ i ∈ s, MeasurableSet (A i))
  (hsym : ∀ i ∈ s, μ.real (A i) = μ.real (A i₀))
  (hc : 0 ≤ c)
  (hn : 1 ≤ n)
  (hunion : 1 - μ.real (⋃ i ∈ s, A i) ≤ c * (n : ℝ) ^ (-ε)) :
-- imply
  1 - c ^ ((1 : ℝ) / s.card) * (n : ℝ) ^ (-ε / s.card) ≤ μ.real (A i₀) := by
-- proof
  apply StatMech.BeffaraDC.finite_symmetric_polynomial_deficit μ hpa s A hi₀ hA hAm hsym hc hn hunion


-- created on 2026-10-23
