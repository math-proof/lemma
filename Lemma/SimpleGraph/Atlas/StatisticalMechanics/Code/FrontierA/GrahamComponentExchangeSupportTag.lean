import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeSupportTag
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[componentExchangeSupportTag_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeSupportTag.lean)
-/
@[path]
private lemma componentExchangeSupportTag_injective_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero) :
-- imply
  Function.Injective (componentExchangeSupportTag ends m j k l zero hloop hjk hkl hk0) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.componentExchangeSupportTag_injective ends m j k l zero hloop hjk hkl hk0

/--
[card_leftRowSupportIndex_le_rightRowData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeSupportTag.lean)
-/
@[path]
private lemma card_leftRowSupportIndex_le_rightRowData_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero) :
-- imply
  Fintype.card (leftRowSupportIndex ends m j k l zero) ≤ Fintype.card (rightRowData ends m j k l zero) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_leftRowSupportIndex_le_rightRowData ends m j k l zero hloop hjk hkl hk0


-- created on 2026-10-23
