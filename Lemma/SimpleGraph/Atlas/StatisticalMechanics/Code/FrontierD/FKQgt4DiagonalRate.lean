import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKQgt4DiagonalRate
open MeasureTheory Filter Topology StatMech StatMech.FrontierD


/--
[fkQgt4ExactDiagonalSite_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiagonalRate.lean)
-/
@[path]
private lemma fkQgt4ExactDiagonalSite_zero_eq :
-- imply
  fkQgt4ExactDiagonalSite 0 = origin 2 := by
-- proof
  apply StatMech.FrontierD.fkQgt4ExactDiagonalSite_zero

/--
[fkQgt4ExactDiagonalSite_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiagonalRate.lean)
-/
@[path]
private lemma fkQgt4ExactDiagonalSite_add_eq
  {m n : Nat} :
-- imply
  fkQgt4ExactDiagonalSite (m + n) = fkQgt4ExactDiagonalSite m + fkQgt4ExactDiagonalSite n := by
-- proof
  apply StatMech.FrontierD.fkQgt4ExactDiagonalSite_add m n

/--
[fkQgt4CriticalFreeExactDiagonalTwoPoint_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiagonalRate.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeExactDiagonalTwoPoint_pos_eq
  {q : Real}
  {n : Nat}
-- given
  (hq : 4 < q) :
-- imply
  0 < fkQgt4CriticalFreeExactDiagonalTwoPoint hq n := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeExactDiagonalTwoPoint_pos hq n

/--
[fkQgt4CriticalFreeExactDiagonalTwoPoint_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiagonalRate.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeExactDiagonalTwoPoint_le_one_eq
  {q : Real}
  {n : Nat}
-- given
  (hq : 4 < q) :
-- imply
  fkQgt4CriticalFreeExactDiagonalTwoPoint hq n <= 1 := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeExactDiagonalTwoPoint_le_one hq n

/--
[infiniteTwoPointReal_add_eq_of_translationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiagonalRate.lean)
-/
@[path]
private lemma infiniteTwoPointReal_add_eq_of_translationInvariant_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
  {a x y : Site d}
-- given
  (htrans : ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
-- imply
  FK.infiniteTwoPointReal mu (a + x) (a + y) = FK.infiniteTwoPointReal mu x y := by
-- proof
  apply StatMech.FrontierD.infiniteTwoPointReal_add_eq_of_translationInvariant mu htrans a x y

/--
[fkQgt4CriticalFreeExactDiagonalTwoPoint_supermultiplicative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiagonalRate.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeExactDiagonalTwoPoint_supermultiplicative_eq
  {q : Real}
  {m n : Nat}
-- given
  (hq : 4 < q) :
-- imply
  fkQgt4CriticalFreeExactDiagonalTwoPoint hq m * fkQgt4CriticalFreeExactDiagonalTwoPoint hq n <= fkQgt4CriticalFreeExactDiagonalTwoPoint hq (m + n) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeExactDiagonalTwoPoint_supermultiplicative hq m n

/--
[fkQgt4CriticalFreeExactDiagonalNegLog_subadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiagonalRate.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeExactDiagonalNegLog_subadditive_eq
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  Subadditive (fun n => -Real.log (fkQgt4CriticalFreeExactDiagonalTwoPoint hq n)) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeExactDiagonalNegLog_subadditive hq

/--
[fkQgt4CriticalFreeExactDiagonalNegLog_bddBelow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiagonalRate.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeExactDiagonalNegLog_bddBelow_eq
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  BddBelow (Set.range (fun n => -Real.log (fkQgt4CriticalFreeExactDiagonalTwoPoint hq n) / (n : Real))) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeExactDiagonalNegLog_bddBelow hq

/--
[fkQgt4CriticalFreeExactDiagonalRate_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiagonalRate.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeExactDiagonalRate_tendsto_eq
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  Tendsto (fun n => -Real.log (fkQgt4CriticalFreeExactDiagonalTwoPoint hq n) / (n : Real)) atTop (nhds (fkQgt4CriticalFreeExactDiagonalRateLimit hq)) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeExactDiagonalRate_tendsto hq

/--
[tendsto_add_one_div_two_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiagonalRate.lean)
-/
@[path]
private lemma tendsto_add_one_div_two_atTop_eq :
-- imply
  Tendsto (fun n : Nat => (n + 1) / 2) atTop atTop := by
-- proof
  apply StatMech.FrontierD.tendsto_add_one_div_two_atTop

/--
[tendsto_cast_add_one_div_two_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiagonalRate.lean)
-/
@[path]
private lemma tendsto_cast_add_one_div_two_ratio_eq :
-- imply
  Tendsto (fun n : Nat => (((n + 1) / 2 : Nat) : Real) / (n + 1 : Real)) atTop (nhds (1 / 2 : Real)) := by
-- proof
  apply StatMech.FrontierD.tendsto_cast_add_one_div_two_ratio

/--
[fkQgt4DiagonalSite_eq_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiagonalRate.lean)
-/
@[path]
private lemma fkQgt4DiagonalSite_eq_exact_eq
  {n : Nat} :
-- imply
  fkQgt4DiagonalSite n = fkQgt4ExactDiagonalSite (n / 2) := by
-- proof
  apply StatMech.FrontierD.fkQgt4DiagonalSite_eq_exact n

/--
[fkQgt4CriticalFreeDiagonalTwoPoint_eq_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiagonalRate.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeDiagonalTwoPoint_eq_exact_eq
  {q : Real}
  {n : Nat}
-- given
  (hq : 4 < q) :
-- imply
  fkQgt4CriticalFreeDiagonalTwoPoint hq n = fkQgt4CriticalFreeExactDiagonalTwoPoint hq (n / 2) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeDiagonalTwoPoint_eq_exact hq n

/--
[fkQgt4CriticalFreeDiagonalRate_tendsto_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiagonalRate.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeDiagonalRate_tendsto_unconditional_eq
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeDiagonalRate_tendsto_unconditional hq

/--
[fkQgt4CriticalFreeExactDiagonalRateLimit_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiagonalRate.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeExactDiagonalRateLimit_nonneg_eq
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  0 <= fkQgt4CriticalFreeExactDiagonalRateLimit hq := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeExactDiagonalRateLimit_nonneg hq


-- created on 2026-10-23
