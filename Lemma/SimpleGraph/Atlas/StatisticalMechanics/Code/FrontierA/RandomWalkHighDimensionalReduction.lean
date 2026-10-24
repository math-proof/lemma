import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.RandomWalkHighDimensionalReduction
open Filter Finset Topology StatMech StatMech.FrontierA


/--
[randomWalkIterate_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensionalReduction.lean)
-/
@[path]
private lemma randomWalkIterate_zero_eq
  {T : PositiveAdditiveOperator X}
  {f : X → ℝ} :
-- imply
  randomWalkIterate T 0 f = f := by
-- proof
  apply StatMech.FrontierA.randomWalkIterate_zero T f

/--
[randomWalkIterate_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensionalReduction.lean)
-/
@[path]
private lemma randomWalkIterate_succ_eq
  {T : PositiveAdditiveOperator X}
  {n : ℕ}
  {f : X → ℝ} :
-- imply
  randomWalkIterate T (n + 1) f = T (randomWalkIterate T n f) := by
-- proof
  apply StatMech.FrontierA.randomWalkIterate_succ T n f

/--
[randomWalkPartial_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensionalReduction.lean)
-/
@[path]
private lemma randomWalkPartial_zero_eq
  {T : PositiveAdditiveOperator X}
  {delta : X → ℝ} :
-- imply
  randomWalkPartial T delta 0 = 0 := by
-- proof
  apply StatMech.FrontierA.randomWalkPartial_zero T delta

/--
[randomWalkPartial_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensionalReduction.lean)
-/
@[path]
private lemma randomWalkPartial_succ_eq
  {T : PositiveAdditiveOperator X}
  {delta : X → ℝ}
  {n : ℕ} :
-- imply
  randomWalkPartial T delta (n + 1) = delta + T (randomWalkPartial T delta n) := by
-- proof
  apply StatMech.FrontierA.randomWalkPartial_succ T delta n

/--
[randomWalkPartial_succ_eq_add_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensionalReduction.lean)
-/
@[path]
private lemma randomWalkPartial_succ_eq_add_iterate_eq
  {T : PositiveAdditiveOperator X}
  {delta : X → ℝ}
  {n : ℕ} :
-- imply
  randomWalkPartial T delta (n + 1) = randomWalkPartial T delta n + randomWalkIterate T n delta := by
-- proof
  apply StatMech.FrontierA.randomWalkPartial_succ_eq_add_iterate T delta n

/--
[randomWalkPartial_eq_sum_iterates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensionalReduction.lean)
-/
@[path]
private lemma randomWalkPartial_eq_sum_iterates_eq
  {T : PositiveAdditiveOperator X}
  {delta : X → ℝ}
  {n : ℕ} :
-- imply
  randomWalkPartial T delta n = ∑ k ∈ Finset.range n, randomWalkIterate T k delta := by
-- proof
  apply StatMech.FrontierA.randomWalkPartial_eq_sum_iterates T delta n

/--
[randomWalkIterate_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensionalReduction.lean)
-/
@[path]
private lemma randomWalkIterate_nonneg_eq
  {T : PositiveAdditiveOperator X}
  {f : X → ℝ}
-- given
  (hf : ∀ x, 0 ≤ f x) :
-- imply
  ∀ n x, 0 ≤ randomWalkIterate T n f x := by
-- proof
  apply StatMech.FrontierA.randomWalkIterate_nonneg T f hf

/--
[randomWalkPartial_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensionalReduction.lean)
-/
@[path]
private lemma randomWalkPartial_nonneg_eq
  {T : PositiveAdditiveOperator X}
  {delta : X → ℝ}
-- given
  (hdelta : ∀ x, 0 ≤ delta x) :
-- imply
  ∀ n x, 0 ≤ randomWalkPartial T delta n x := by
-- proof
  apply StatMech.FrontierA.randomWalkPartial_nonneg T delta hdelta

/--
[renewal_le_partial_add_remainder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensionalReduction.lean)
-/
@[path]
private lemma renewal_le_partial_add_remainder_eq
  {T : PositiveAdditiveOperator X}
  {delta twoPoint : X → ℝ}
-- given
  (hrenewal : ∀ x, twoPoint x ≤ delta x + T twoPoint x) :
-- imply
  ∀ n x, twoPoint x ≤ randomWalkPartial T delta n x + randomWalkIterate T n twoPoint x := by
-- proof
  apply StatMech.FrontierA.renewal_le_partial_add_remainder T delta twoPoint hrenewal

/--
[renewal_le_effectiveRandomWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensionalReduction.lean)
-/
@[path]
private lemma renewal_le_effectiveRandomWalk_eq
  {T : PositiveAdditiveOperator X}
  {delta twoPoint green : X → ℝ}
-- given
  (hrenewal : ∀ x, twoPoint x ≤ delta x + T twoPoint x)
  (hpartial : ∀ x, Tendsto (fun n => randomWalkPartial T delta n x) atTop (nhds (green x)))
  (hremainder : ∀ x, Tendsto (fun n => randomWalkIterate T n twoPoint x) atTop (nhds 0)) :
-- imply
  ∀ x, twoPoint x ≤ green x := by
-- proof
  apply StatMech.FrontierA.renewal_le_effectiveRandomWalk T delta twoPoint green hrenewal hpartial hremainder

/--
[effectiveRandomWalk_bound_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensionalReduction.lean)
-/
@[path]
private lemma effectiveRandomWalk_bound_transfer_eq
  {d : ℕ}
  {epsilon sigma C c xi : ℝ}
  {delta twoPoint green radius : X → ℝ}
-- given
  (hdomination : ∀ x, twoPoint x ≤ green x)
  (hgreen : ∀ x, green x ≤ delta x + highDimensionalRandomWalkTail d epsilon sigma C c xi (radius x)) :
-- imply
  ∀ x, twoPoint x ≤ delta x + highDimensionalRandomWalkTail d epsilon sigma C c xi (radius x) := by
-- proof
  apply StatMech.FrontierA.effectiveRandomWalk_bound_transfer d epsilon sigma C c xi delta twoPoint green radius hdomination hgreen

/--
[renewal_to_highDimensionalRandomWalk_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensionalReduction.lean)
-/
@[path]
private lemma renewal_to_highDimensionalRandomWalk_bound_eq
  {T : PositiveAdditiveOperator X}
  {d : ℕ}
  {epsilon sigma C c xi : ℝ}
  {delta twoPoint green radius : X → ℝ}
-- given
  (hrenewal : ∀ x, twoPoint x ≤ delta x + T twoPoint x)
  (hpartial : ∀ x, Tendsto (fun n => randomWalkPartial T delta n x) atTop (nhds (green x)))
  (hremainder : ∀ x, Tendsto (fun n => randomWalkIterate T n twoPoint x) atTop (nhds 0))
  (hgreen : ∀ x, green x ≤ delta x + highDimensionalRandomWalkTail d epsilon sigma C c xi (radius x)) :
-- imply
  ∀ x, twoPoint x ≤ delta x + highDimensionalRandomWalkTail d epsilon sigma C c xi (radius x) := by
-- proof
  apply StatMech.FrontierA.renewal_to_highDimensionalRandomWalk_bound T d epsilon sigma C c xi delta twoPoint green radius hrenewal hpartial hremainder hgreen


-- created on 2026-10-23
