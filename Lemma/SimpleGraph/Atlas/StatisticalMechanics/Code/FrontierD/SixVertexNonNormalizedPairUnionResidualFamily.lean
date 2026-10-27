import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexNonNormalizedPairUnionResidualFamily.Part4
open StatMech StatMech.FrontierD StatMech.FrontierD.SixVertexNonNormalizedPairUnionPhysicalTargetFamily


/--
[SixVertexNonNormalizedUnitChargeResidualSources.unitCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexNonNormalizedPairUnionResidualFamily.lean)
-/
@[path]
private lemma unitCharge_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexNonNormalizedUnitChargeResidualSources T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  sixVertexHorizontalDegreeTwoUnitCharge source.1.1 := by
-- proof
  apply StatMech.FrontierD.SixVertexNonNormalizedUnitChargeResidualSources.unitCharge source

/--
[surplusTarget_physical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexNonNormalizedPairUnionResidualFamily.lean)
-/
@[path]
private lemma surplusTarget_physical_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle hmiddle_pos hmiddle_lt grade}
  {coded : SixVertexNonNormalizedUnitChargeResidualSources T middle hmiddle_pos hmiddle_lt grade × Bool} :
-- imply
  sixVertexHorizontalActualSurplusConfigurationPair (family.surplusTarget coded) = family.target coded := by
-- proof
  apply StatMech.FrontierD.SixVertexNonNormalizedPairUnionPhysicalTargetFamily.surplusTarget_physical family coded

/--
[decode_surplusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexNonNormalizedPairUnionResidualFamily.lean)
-/
@[path]
private lemma decode_surplusTarget_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexNonNormalizedUnitChargeResidualSources T middle hmiddle_pos hmiddle_lt grade}
  {branch : Bool} :
-- imply
  family.decoder (family.surplusTarget (source, branch)) = some source.1.1 := by
-- proof
  apply StatMech.FrontierD.SixVertexNonNormalizedPairUnionPhysicalTargetFamily.decode_surplusTarget family source branch

/--
[surplusTarget_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexNonNormalizedPairUnionResidualFamily.lean)
-/
@[path]
private lemma surplusTarget_supported_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexNonNormalizedUnitChargeResidualSources T middle hmiddle_pos hmiddle_lt grade}
  {branch : Bool} :
-- imply
  sixVertexHorizontalOffDiagonalTwoCycleSupport T middle hmiddle_pos hmiddle_lt grade source.1.1 (family.surplusTarget (source, branch)) := by
-- proof
  apply StatMech.FrontierD.SixVertexNonNormalizedPairUnionPhysicalTargetFamily.surplusTarget_supported family source branch

/--
[surplusTarget_joint_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexNonNormalizedPairUnionResidualFamily.lean)
-/
@[path]
private lemma surplusTarget_joint_injective_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  Function.Injective (fun coded => family.surplusTarget coded) := by
-- proof
  apply StatMech.FrontierD.SixVertexNonNormalizedPairUnionPhysicalTargetFamily.surplusTarget_joint_injective family

/--
[surplusTarget_branch_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexNonNormalizedPairUnionResidualFamily.lean)
-/
@[path]
private lemma surplusTarget_branch_injective_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle hmiddle_pos hmiddle_lt grade}
  {branch : Bool} :
-- imply
  Function.Injective (fun source => family.surplusTarget (source, branch)) := by
-- proof
  apply StatMech.FrontierD.SixVertexNonNormalizedPairUnionPhysicalTargetFamily.surplusTarget_branch_injective family branch

/--
[surplusTarget_branches_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexNonNormalizedPairUnionResidualFamily.lean)
-/
@[path]
private lemma surplusTarget_branches_disjoint_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle hmiddle_pos hmiddle_lt grade}
  {first second : SixVertexNonNormalizedUnitChargeResidualSources T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  family.surplusTarget (first, false) ≠ family.surplusTarget (second, true) := by
-- proof
  apply StatMech.FrontierD.SixVertexNonNormalizedPairUnionPhysicalTargetFamily.surplusTarget_branches_disjoint family first second

/--
[geometricRepair_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexNonNormalizedPairUnionResidualFamily.lean)
-/
@[path]
private lemma geometricRepair_target_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexNonNormalizedUnitChargeResidualSources T middle hmiddle_pos hmiddle_lt grade}
  {branch : Bool} :
-- imply
  (family.geometricRepair source branch).target = family.surplusTarget (source, branch) := by
-- proof
  apply StatMech.FrontierD.SixVertexNonNormalizedPairUnionPhysicalTargetFamily.geometricRepair_target family source branch


-- created on 2026-10-23
