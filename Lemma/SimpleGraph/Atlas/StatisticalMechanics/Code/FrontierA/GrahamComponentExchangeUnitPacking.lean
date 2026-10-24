import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeUnitPacking
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[rightRowDataIndexFiber_card_eq_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeUnitPacking.lean)
-/
@[path]
private lemma rightRowDataIndexFiber_card_eq_weight_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {R : rightRowSupportIndex ends m j k l zero} :
-- imply
  Fintype.card (rightRowDataIndexFiber ends m j k l zero R) = rowSupportWeight ends m R.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightRowDataIndexFiber_card_eq_weight ends m j k l zero R

/--
[card_componentExchangeSupportFiber_le_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeUnitPacking.lean)
-/
@[path]
private lemma card_componentExchangeSupportFiber_le_weight_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {R : rightRowSupportIndex ends m j k l zero}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero) :
-- imply
  Fintype.card (componentExchangeSupportFiber ends m j k l zero R) ≤ rowSupportWeight ends m R.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_componentExchangeSupportFiber_le_weight ends m j k l zero hloop hjk hkl hk0 R

/--
[leftRowData_card_eq_leftRowSupportIndex_of_unit_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeUnitPacking.lean)
-/
@[path]
private lemma leftRowData_card_eq_leftRowSupportIndex_of_unit_weight_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
-- given
  (hunit : ∀ K ⊆ m, LeftRowSupport ends m j k l zero K → rowSupportWeight ends m K = 1) :
-- imply
  Fintype.card (leftRowData ends m j k l zero) = Fintype.card (leftRowSupportIndex ends m j k l zero) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftRowData_card_eq_leftRowSupportIndex_of_unit_weight ends m j k l zero hunit

/--
[GrahamWeightedRowMinor_of_unit_left_support_weights](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeUnitPacking.lean)
-/
@[path]
private lemma GrahamWeightedRowMinor_of_unit_left_support_weights_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hunit : ∀ K ⊆ m, LeftRowSupport ends m j k l zero K → rowSupportWeight ends m K = 1) :
-- imply
  GrahamWeightedRowMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamWeightedRowMinor_of_unit_left_support_weights ends m j k l zero hloop hjk hkl hk0 hunit


-- created on 2026-10-23
