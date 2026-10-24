import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.WiredDenominatorArithmetic
open Finset StatMech StatMech.OSSS


/--
[antitone_sum_Ico_one_le_two_sum_Icc_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredDenominatorArithmetic.lean)
-/
@[path]
private lemma antitone_sum_Ico_one_le_two_sum_Icc_half_eq
  {n : Nat}
-- given
  (a : Nat -> Real)
  (ha0 : forall k, 0 <= a k)
  (hanti : Antitone a) :
-- imply
  (∑ k ∈ Ico 1 n, a k) <= 2 * ∑ k ∈ Icc 1 (n / 2), a k := by
-- proof
  apply StatMech.OSSS.antitone_sum_Ico_one_le_two_sum_Icc_half a ha0 hanti n

/--
[antitone_sum_Ico_one_le_two_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredDenominatorArithmetic.lean)
-/
@[path]
private lemma antitone_sum_Ico_one_le_two_profile_eq
  {n : Nat}
-- given
  (a theta : Nat -> Real)
  (ha0 : forall k, 0 <= a k)
  (hanti : Antitone a)
  (htheta0 : forall k, 0 <= theta k)
  (hcomp : forall k, k ∈ Icc 1 (n / 2) -> a k <= theta k) :
-- imply
  (∑ k ∈ Ico 1 n, a k) <= 2 * ∑ k ∈ range n, theta k := by
-- proof
  apply StatMech.OSSS.antitone_sum_Ico_one_le_two_profile a theta ha0 hanti htheta0 n hcomp

/--
[antitone_sum_range_le_two_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredDenominatorArithmetic.lean)
-/
@[path]
private lemma antitone_sum_range_le_two_profile_eq
  {n : Nat}
-- given
  (a theta : Nat -> Real)
  (ha0 : forall k, 0 <= a k)
  (hanti : Antitone a)
  (htheta0 : forall k, 0 <= theta k)
  (hzero : a 0 <= theta 0)
  (hcomp : forall k, k ∈ Icc 1 (n / 2) -> a k <= theta k) :
-- imply
  (∑ k ∈ range n, a k) <= 2 * ∑ k ∈ range n, theta k := by
-- proof
  apply StatMech.OSSS.antitone_sum_range_le_two_profile a theta ha0 hanti htheta0 n hzero hcomp

/--
[antitone_sum_range_le_two_profile_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredDenominatorArithmetic.lean)
-/
@[path]
private lemma antitone_sum_range_le_two_profile_strict_eq
  {n : Nat}
-- given
  (a theta : Nat -> Real)
  (ha0 : forall k, 0 <= a k)
  (hanti : Antitone a)
  (htheta0 : forall k, 0 <= theta k)
  (hzero : a 0 <= theta 0)
  (hcomp : forall k, k ∈ Icc 1 (n / 2) -> 2 * k < n -> a k <= theta k)
  (hmiddle : forall k, 2 * k = n -> a k <= theta 0) :
-- imply
  (∑ k ∈ range n, a k) <= 2 * ∑ k ∈ range n, theta k := by
-- proof
  apply StatMech.OSSS.antitone_sum_range_le_two_profile_strict a theta ha0 hanti htheta0 n hzero hcomp hmiddle


-- created on 2026-10-23
