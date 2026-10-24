import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.PermCycleQuotientCount
open StatMech StatMech.FrontierA


/--
[permCycleRepresentativeOf_eq_iff_sameCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/PermCycleQuotientCount.lean)
-/
@[path]
private lemma permCycleRepresentativeOf_eq_iff_sameCycle_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Perm D}
  {x y : D} :
-- imply
  permCycleRepresentativeOf sigma x = permCycleRepresentativeOf sigma y ↔ sigma.SameCycle x y := by
-- proof
  apply StatMech.FrontierA.permCycleRepresentativeOf_eq_iff_sameCycle sigma x y

/--
[permCycleRepresentativeOf_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/PermCycleQuotientCount.lean)
-/
@[path]
private lemma permCycleRepresentativeOf_surjective_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Perm D} :
-- imply
  Function.Surjective (permCycleRepresentativeOf sigma) := by
-- proof
  apply StatMech.FrontierA.permCycleRepresentativeOf_surjective sigma

/--
[natCard_permCycleClass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/PermCycleQuotientCount.lean)
-/
@[path]
private lemma natCard_permCycleClass_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Perm D} :
-- imply
  Nat.card (PermCycleClass sigma) = permCycleCount sigma := by
-- proof
  apply StatMech.FrontierA.natCard_permCycleClass sigma

/--
[four_mul_permCycleCount_eq_card_of_pow_four_eq_one_of_sq_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/PermCycleQuotientCount.lean)
-/
@[path]
private lemma four_mul_permCycleCount_eq_card_of_pow_four_eq_one_of_sq_ne_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Perm D}
-- given
  (h4 : sigma ^ 4 = 1)
  (h2 : ∀ x, (sigma ^ 2) x ≠ x) :
-- imply
  4 * permCycleCount sigma = Fintype.card D := by
-- proof
  apply StatMech.FrontierA.four_mul_permCycleCount_eq_card_of_pow_four_eq_one_of_sq_ne sigma h4 h2


-- created on 2026-10-23
