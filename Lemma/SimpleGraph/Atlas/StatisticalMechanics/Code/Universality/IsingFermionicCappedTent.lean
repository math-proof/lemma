import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicCappedTent
open StatMech StatMech.Universality


/--
[isingNatCappedTent_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCappedTent.lean)
-/
@[path]
private lemma isingNatCappedTent_nonneg_eq
  {source i : Nat} :
-- imply
  0 <= isingNatCappedTent source i := by
-- proof
  apply StatMech.Universality.isingNatCappedTent_nonneg source i

/--
[isingNatCappedTent_le_coordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCappedTent.lean)
-/
@[path]
private lemma isingNatCappedTent_le_coordinate_eq
  {source i : Nat} :
-- imply
  isingNatCappedTent source i <= (i : Real) := by
-- proof
  apply StatMech.Universality.isingNatCappedTent_le_coordinate source i

/--
[isingNatCappedTent_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCappedTent.lean)
-/
@[path]
private lemma isingNatCappedTent_self_eq
  {source : Nat} :
-- imply
  isingNatCappedTent source source = (source : Real) := by
-- proof
  apply StatMech.Universality.isingNatCappedTent_self source

/--
[isingNatCappedRobinTent_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCappedTent.lean)
-/
@[path]
private lemma isingNatCappedRobinTent_nonneg_eq
  {coefficient : Real}
  {source i : Nat}
-- given
  (hcoefficient : 0 < coefficient) :
-- imply
  0 <= isingNatCappedRobinTent coefficient source i := by
-- proof
  apply StatMech.Universality.isingNatCappedRobinTent_nonneg coefficient hcoefficient source i

/--
[isingNatCappedTent_secondDifference_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCappedTent.lean)
-/
@[path]
private lemma isingNatCappedTent_secondDifference_nonpos_eq
  {source i : Nat}
-- given
  (hi : 0 < i) :
-- imply
  isingNatCappedTent source (i + 1) + isingNatCappedTent source (i - 1) - 2 * isingNatCappedTent source i <= 0 := by
-- proof
  apply StatMech.Universality.isingNatCappedTent_secondDifference_nonpos source i hi

/--
[isingNatCappedTent_secondDifference_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCappedTent.lean)
-/
@[path]
private lemma isingNatCappedTent_secondDifference_source_eq
  {source : Nat}
-- given
  (hsource : 0 < source) :
-- imply
  isingNatCappedTent source (source + 1) + isingNatCappedTent source (source - 1) - 2 * isingNatCappedTent source source = -1 := by
-- proof
  apply StatMech.Universality.isingNatCappedTent_secondDifference_source source hsource

/--
[isingNatCappedRobinTent_secondDifference_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCappedTent.lean)
-/
@[path]
private lemma isingNatCappedRobinTent_secondDifference_nonpos_eq
  {coefficient : Real}
  {source i : Nat}
-- given
  (hi : 0 < i) :
-- imply
  isingNatCappedRobinTent coefficient source (i + 1) + isingNatCappedRobinTent coefficient source (i - 1) - 2 * isingNatCappedRobinTent coefficient source i <= 0 := by
-- proof
  apply StatMech.Universality.isingNatCappedRobinTent_secondDifference_nonpos coefficient source i hi

/--
[isingNatCappedRobinTent_secondDifference_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCappedTent.lean)
-/
@[path]
private lemma isingNatCappedRobinTent_secondDifference_source_eq
  {coefficient : Real}
  {source : Nat}
-- given
  (hsource : 0 < source) :
-- imply
  isingNatCappedRobinTent coefficient source (source + 1) + isingNatCappedRobinTent coefficient source (source - 1) - 2 * isingNatCappedRobinTent coefficient source source = -1 := by
-- proof
  apply StatMech.Universality.isingNatCappedRobinTent_secondDifference_source coefficient source hsource

/--
[isingNatCappedRobinTent_left_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCappedTent.lean)
-/
@[path]
private lemma isingNatCappedRobinTent_left_balance_eq
  {coefficient : Real}
  {source : Nat}
-- given
  (hcoefficient : 0 < coefficient)
  (hsource : 0 < source) :
-- imply
  isingNatCappedRobinTent coefficient source 1 - isingNatCappedRobinTent coefficient source 0 - coefficient * isingNatCappedRobinTent coefficient source 0 = 0 := by
-- proof
  apply StatMech.Universality.isingNatCappedRobinTent_left_balance coefficient hcoefficient source hsource

/--
[isingNatCappedTent_predecessor_sub_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCappedTent.lean)
-/
@[path]
private lemma isingNatCappedTent_predecessor_sub_nonpos_eq
  {source i : Nat} :
-- imply
  isingNatCappedTent source (i - 1) - isingNatCappedTent source i <= 0 := by
-- proof
  apply StatMech.Universality.isingNatCappedTent_predecessor_sub_nonpos source i

/--
[isingNatCappedRobinTent_predecessor_sub_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCappedTent.lean)
-/
@[path]
private lemma isingNatCappedRobinTent_predecessor_sub_nonpos_eq
  {coefficient : Real}
  {source i : Nat} :
-- imply
  isingNatCappedRobinTent coefficient source (i - 1) - isingNatCappedRobinTent coefficient source i <= 0 := by
-- proof
  apply StatMech.Universality.isingNatCappedRobinTent_predecessor_sub_nonpos coefficient source i

/--
[isingNatReverseCappedTent_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCappedTent.lean)
-/
@[path]
private lemma isingNatReverseCappedTent_nonneg_eq
  {top source i : Nat} :
-- imply
  0 <= isingNatReverseCappedTent top source i := by
-- proof
  apply StatMech.Universality.isingNatReverseCappedTent_nonneg top source i

/--
[isingNatReverseCappedTent_le_coordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCappedTent.lean)
-/
@[path]
private lemma isingNatReverseCappedTent_le_coordinate_eq
  {top source i : Nat} :
-- imply
  isingNatReverseCappedTent top source i <= (top - i : Nat) := by
-- proof
  apply StatMech.Universality.isingNatReverseCappedTent_le_coordinate top source i

/--
[isingNatReverseCappedTent_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCappedTent.lean)
-/
@[path]
private lemma isingNatReverseCappedTent_self_eq
  {top source : Nat} :
-- imply
  isingNatReverseCappedTent top source source = (top - source : Nat) := by
-- proof
  apply StatMech.Universality.isingNatReverseCappedTent_self top source

/--
[isingNatReverseCappedTent_secondDifference_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCappedTent.lean)
-/
@[path]
private lemma isingNatReverseCappedTent_secondDifference_nonpos_eq
  {top source i : Nat}
-- given
  (hi : 0 < i)
  (hitop : i < top) :
-- imply
  isingNatReverseCappedTent top source (i + 1) + isingNatReverseCappedTent top source (i - 1) - 2 * isingNatReverseCappedTent top source i <= 0 := by
-- proof
  apply StatMech.Universality.isingNatReverseCappedTent_secondDifference_nonpos top source i hi hitop

/--
[isingNatReverseCappedTent_secondDifference_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCappedTent.lean)
-/
@[path]
private lemma isingNatReverseCappedTent_secondDifference_source_eq
  {top source : Nat}
-- given
  (hsource : 0 < source)
  (hsourceTop : source < top) :
-- imply
  isingNatReverseCappedTent top source (source + 1) + isingNatReverseCappedTent top source (source - 1) - 2 * isingNatReverseCappedTent top source source = -1 := by
-- proof
  apply StatMech.Universality.isingNatReverseCappedTent_secondDifference_source top source hsource hsourceTop


-- created on 2026-10-23
