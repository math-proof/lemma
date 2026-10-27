import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.CellGaussBonnet.Part3
open StatMech StatMech.Onsager StatMech.Onsager.CellGaussBonnet


/--
[cornerDiff_cex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellGaussBonnet.lean)
-/
@[path]
private lemma cornerDiff_cex_eq :
-- imply
  cornerDiff ({((0:ℤ), (0:ℤ)), ((1:ℤ), (1:ℤ))} : Finset (ℤ × ℤ)) = 6 := by
-- proof
  apply StatMech.Onsager.CellGaussBonnet.cornerDiff_cex

/--
[eulerChar_cex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellGaussBonnet.lean)
-/
@[path]
private lemma eulerChar_cex_eq :
-- imply
  eulerChar ({((0:ℤ), (0:ℤ)), ((1:ℤ), (1:ℤ))} : Finset (ℤ × ℤ)) = 1 := by
-- proof
  apply StatMech.Onsager.CellGaussBonnet.eulerChar_cex

/--
[gaussBonnet_stated_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellGaussBonnet.lean)
-/
@[path]
private lemma gaussBonnet_stated_false_eq :
-- imply
  ¬ ∀ S : Finset (ℤ × ℤ), cornerDiff S = 4 * eulerChar S := by
-- proof
  apply StatMech.Onsager.CellGaussBonnet.gaussBonnet_stated_false

/--
[localIdentity_stated_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellGaussBonnet.lean)
-/
@[path]
private lemma localIdentity_stated_false_eq :
-- imply
  ¬ ∀ e w n s ne nw se sw : Bool, lhsLocal e w n s ne nw se sw = rhsStated e w n s ne nw se sw := by
-- proof
  apply StatMech.Onsager.CellGaussBonnet.localIdentity_stated_false

/--
[localIdentity_corrected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellGaussBonnet.lean)
-/
@[path]
private lemma localIdentity_corrected_eq :
-- imply
  ∀ e w n s ne nw se sw : Bool, lhsLocal e w n s ne nw se sw = rhsCorrected e w n s ne nw se sw := by
-- proof
  apply StatMech.Onsager.CellGaussBonnet.localIdentity_corrected


-- created on 2026-10-23
