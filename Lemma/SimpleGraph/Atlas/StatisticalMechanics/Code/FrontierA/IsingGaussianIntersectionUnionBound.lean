import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianIntersectionUnionBound.Part2
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[finiteTreeSeparatedFourMass_eq_summand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIntersectionUnionBound.lean)
-/
@[path]
private lemma finiteTreeSeparatedFourMass_eq_summand_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l y : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  finiteTreeSeparatedFourMass G beta J i j k l y = ∑' z : TreeFourProfiles G, finiteTreeSeparatedFourSummand G beta J i j k l y z := by
-- proof
  apply StatMech.FrontierA.finiteTreeSeparatedFourMass_eq_summand G beta J i j k l y

/--
[finiteTreeIndependentIntersectionSummand_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIntersectionUnionBound.lean)
-/
@[path]
private lemma finiteTreeIndependentIntersectionSummand_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
  {z : TreeFourProfiles G}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e) :
-- imply
  0 <= finiteTreeIndependentIntersectionSummand G beta J i j k l z := by
-- proof
  apply StatMech.FrontierA.finiteTreeIndependentIntersectionSummand_nonneg G beta J hbeta hJ i j k l z

/--
[summable_finiteTreeIndependentIntersectionSummand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIntersectionUnionBound.lean)
-/
@[path]
private lemma summable_finiteTreeIndependentIntersectionSummand_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  Summable (finiteTreeIndependentIntersectionSummand G beta J i j k l) := by
-- proof
  apply StatMech.FrontierA.summable_finiteTreeIndependentIntersectionSummand G beta J i j k l

/--
[finiteTreeSeparatedFourSummand_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIntersectionUnionBound.lean)
-/
@[path]
private lemma finiteTreeSeparatedFourSummand_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l y : V}
  {z : TreeFourProfiles G}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e) :
-- imply
  0 <= finiteTreeSeparatedFourSummand G beta J i j k l y z := by
-- proof
  apply StatMech.FrontierA.finiteTreeSeparatedFourSummand_nonneg G beta J hbeta hJ i j k l y z

/--
[finiteTreeIndependentIntersectionSummand_le_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIntersectionUnionBound.lean)
-/
@[path]
private lemma finiteTreeIndependentIntersectionSummand_le_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
  {z : TreeFourProfiles G}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e) :
-- imply
  finiteTreeIndependentIntersectionSummand G beta J i j k l z <= ∑ y : V, finiteTreeSeparatedFourSummand G beta J i j k l y z := by
-- proof
  apply StatMech.FrontierA.finiteTreeIndependentIntersectionSummand_le_sum G beta J hbeta hJ i j k l z

/--
[finiteTreeIndependentIntersectionFourMass_le_sum_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIntersectionUnionBound.lean)
-/
@[path]
private lemma finiteTreeIndependentIntersectionFourMass_le_sum_separated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e) :
-- imply
  finiteTreeIndependentIntersectionFourMass G beta J i j k l <= ∑ y : V, finiteTreeSeparatedFourMass G beta J i j k l y := by
-- proof
  apply StatMech.FrontierA.finiteTreeIndependentIntersectionFourMass_le_sum_separated G beta J hbeta hJ i j k l


-- created on 2026-10-23
