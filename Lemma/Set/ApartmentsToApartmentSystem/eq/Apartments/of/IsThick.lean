import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Building.AptIsCoxeterProof
open ChamberComplex AptIsCoxeterProof


/--
[PreApartmentData.toApartmentSystem_apartments](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AptIsCoxeterProof.lean)
-/
@[path]
private lemma toApartmentSystem_apartments_eq
  [DecidableEq V]
  {K : ChamberComplex V}
  {pre : PreApartmentData K}
  {tits_thm : TitsTheoremHyp V}
  {thickness_implies_apt : ThicknessImpliesAptStructureHyp V}
-- given
  (hThick : K.IsThick) :
-- imply
  (pre.toApartmentSystem hThick tits_thm thickness_implies_apt).apartments = pre.apartments := by
-- proof
  apply AptIsCoxeterProof.PreApartmentData.toApartmentSystem_apartments pre hThick tits_thm thickness_implies_apt


-- created on 2026-10-23
