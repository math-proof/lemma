import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.ConvexDerivLimit
open Set Filter Topology StatMech StatMech.FK


/--
[cdl_limit_convexOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ConvexDerivLimit.lean)
-/
@[path]
private lemma cdl_limit_convexOn_eq
  {l : Filter κ}
  [l.NeBot]
  {gn : κ → ℝ → ℝ}
  {glim : ℝ → ℝ}
-- given
  (hconv : ∀ i, ConvexOn ℝ univ (gn i))
  (hlim : ∀ x, Tendsto (fun i => gn i x) l (𝓝 (glim x))) :
-- imply
  ConvexOn ℝ univ glim := by
-- proof
  apply StatMech.FK.cdl_limit_convexOn gn glim hconv hlim

/--
[cdl_slope_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ConvexDerivLimit.lean)
-/
@[path]
private lemma cdl_slope_tendsto_eq
  {l : Filter κ}
  {gn : κ → ℝ → ℝ}
  {glim : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hlim : ∀ x, Tendsto (fun i => gn i x) l (𝓝 (glim x))) :
-- imply
  Tendsto (fun i => slope (gn i) a b) l (𝓝 (slope glim a b)) := by
-- proof
  apply StatMech.FK.cdl_slope_tendsto gn glim hlim a b

/--
[cdl_hasDerivWithinAt_rightDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ConvexDerivLimit.lean)
-/
@[path]
private lemma cdl_hasDerivWithinAt_rightDeriv_eq
  {g : ℝ → ℝ}
  {t : ℝ}
-- given
  (hg : ConvexOn ℝ univ g) :
-- imply
  HasDerivWithinAt g (pressureRightDeriv g t) (Ioi t) t := by
-- proof
  apply StatMech.FK.cdl_hasDerivWithinAt_rightDeriv hg t

/--
[cdl_hasDerivWithinAt_leftDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ConvexDerivLimit.lean)
-/
@[path]
private lemma cdl_hasDerivWithinAt_leftDeriv_eq
  {g : ℝ → ℝ}
  {t : ℝ}
-- given
  (hg : ConvexOn ℝ univ g) :
-- imply
  HasDerivWithinAt g (pressureLeftDeriv g t) (Iio t) t := by
-- proof
  apply StatMech.FK.cdl_hasDerivWithinAt_leftDeriv hg t

/--
[cdl_rightDeriv_tendsto_slope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ConvexDerivLimit.lean)
-/
@[path]
private lemma cdl_rightDeriv_tendsto_slope_eq
  {g : ℝ → ℝ}
  {t : ℝ}
-- given
  (hg : ConvexOn ℝ univ g) :
-- imply
  Tendsto (slope g t) (𝓝[>] t) (𝓝 (pressureRightDeriv g t)) := by
-- proof
  apply StatMech.FK.cdl_rightDeriv_tendsto_slope hg t

/--
[cdl_leftDeriv_tendsto_slope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ConvexDerivLimit.lean)
-/
@[path]
private lemma cdl_leftDeriv_tendsto_slope_eq
  {g : ℝ → ℝ}
  {t : ℝ}
-- given
  (hg : ConvexOn ℝ univ g) :
-- imply
  Tendsto (slope g t) (𝓝[<] t) (𝓝 (pressureLeftDeriv g t)) := by
-- proof
  apply StatMech.FK.cdl_leftDeriv_tendsto_slope hg t

/--
[cdl_rightDeriv_eq_sInf_slope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ConvexDerivLimit.lean)
-/
@[path]
private lemma cdl_rightDeriv_eq_sInf_slope_eq
  {g : ℝ → ℝ}
  {t : ℝ}
-- given
  (hg : ConvexOn ℝ univ g) :
-- imply
  pressureRightDeriv g t = sInf (slope g t '' {y | t < y}) := by
-- proof
  apply StatMech.FK.cdl_rightDeriv_eq_sInf_slope hg t

/--
[cdl_leftDeriv_eq_sSup_slope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ConvexDerivLimit.lean)
-/
@[path]
private lemma cdl_leftDeriv_eq_sSup_slope_eq
  {g : ℝ → ℝ}
  {t : ℝ}
-- given
  (hg : ConvexOn ℝ univ g) :
-- imply
  pressureLeftDeriv g t = sSup (slope g t '' {y | y < t}) := by
-- proof
  apply StatMech.FK.cdl_leftDeriv_eq_sSup_slope hg t

/--
[cdl_leftDeriv_le_rightDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ConvexDerivLimit.lean)
-/
@[path]
private lemma cdl_leftDeriv_le_rightDeriv_eq
  {g : ℝ → ℝ}
  {t : ℝ}
-- given
  (hg : ConvexOn ℝ univ g) :
-- imply
  pressureLeftDeriv g t ≤ pressureRightDeriv g t := by
-- proof
  apply StatMech.FK.cdl_leftDeriv_le_rightDeriv hg t

/--
[cdl_rightDeriv_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ConvexDerivLimit.lean)
-/
@[path]
private lemma cdl_rightDeriv_monotone_eq
  {g : ℝ → ℝ}
-- given
  (hg : ConvexOn ℝ univ g) :
-- imply
  Monotone (pressureRightDeriv g) := by
-- proof
  apply StatMech.FK.cdl_rightDeriv_monotone hg

/--
[cdl_leftDeriv_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ConvexDerivLimit.lean)
-/
@[path]
private lemma cdl_leftDeriv_monotone_eq
  {g : ℝ → ℝ}
-- given
  (hg : ConvexOn ℝ univ g) :
-- imply
  Monotone (pressureLeftDeriv g) := by
-- proof
  apply StatMech.FK.cdl_leftDeriv_monotone hg

/--
[cdl_rightDeriv_le_leftDeriv_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ConvexDerivLimit.lean)
-/
@[path]
private lemma cdl_rightDeriv_le_leftDeriv_of_lt_eq
  {g : ℝ → ℝ}
  {z x : ℝ}
-- given
  (hg : ConvexOn ℝ univ g)
  (hzx : z < x) :
-- imply
  pressureRightDeriv g z ≤ pressureLeftDeriv g x := by
-- proof
  apply StatMech.FK.cdl_rightDeriv_le_leftDeriv_of_lt hg hzx

/--
[cdl_countable_leftDeriv_ne_rightDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ConvexDerivLimit.lean)
-/
@[path]
private lemma cdl_countable_leftDeriv_ne_rightDeriv_eq
  {g : ℝ → ℝ}
-- given
  (hg : ConvexOn ℝ univ g) :
-- imply
  {t : ℝ | pressureLeftDeriv g t ≠ pressureRightDeriv g t}.Countable := by
-- proof
  apply StatMech.FK.cdl_countable_leftDeriv_ne_rightDeriv hg

/--
[cdl_convexDerivLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ConvexDerivLimit.lean)
-/
@[path]
private lemma cdl_convexDerivLimit_eq
  {g : ℝ → ℝ}
  {l : Filter κ}
  [l.NeBot]
  {gn : κ → ℝ → ℝ}
  {g : ℝ → ℝ}
-- given
  (hconv : ∀ i, ConvexOn ℝ univ (gn i))
  (hlim : ∀ x, Tendsto (fun i => gn i x) l (𝓝 (g x))) :
-- imply
  ConvexOn ℝ univ g ∧ (∀ t, HasDerivWithinAt g (pressureRightDeriv g t) (Ioi t) t) ∧ (∀ t, HasDerivWithinAt g (pressureLeftDeriv g t) (Iio t) t) ∧ (∀ t, Tendsto (slope g t) (𝓝[>] t) (𝓝 (pressureRightDeriv g t))) ∧ (∀ t, Tendsto (slope g t) (𝓝[<] t) (𝓝 (pressureLeftDeriv g t))) ∧ (∀ a b, Tendsto (fun i => slope (gn i) a b) l (𝓝 (slope g a b))) ∧ (∀ t, pressureLeftDeriv g t ≤ pressureRightDeriv g t) ∧ Monotone (pressureRightDeriv g) ∧ Monotone (pressureLeftDeriv g) ∧ {t : ℝ | pressureLeftDeriv g t ≠ pressureRightDeriv g t}.Countable := by
-- proof
  apply StatMech.FK.cdl_convexDerivLimit gn g hconv hlim


-- created on 2026-10-23
