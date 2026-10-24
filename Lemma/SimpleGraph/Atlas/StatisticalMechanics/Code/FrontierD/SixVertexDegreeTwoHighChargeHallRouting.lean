import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting
open Finset StatMech StatMech.FrontierD


/--
[sixVertexHorizontalDegreeTwo_unitCharge_or_highCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean)
-/
@[path]
private lemma sixVertexHorizontalDegreeTwo_unitCharge_or_highCharge_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoHallSource T middle hmiddle_pos hmiddle_lt grade}
-- given
  (hdegree : SixVertexLocallyDegreeTwo (sixVertexHorizontalActualDeficitConfigurationPair source).1.1.1 (sixVertexHorizontalActualDeficitConfigurationPair source).1.2.1) :
-- imply
  sixVertexHorizontalDegreeTwoUnitCharge source ∨ sixVertexHorizontalDegreeTwoHighCharge source := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalDegreeTwo_unitCharge_or_highCharge source hdegree

/--
[sixVertexHorizontalDegreeTwoUnitCharge_of_not_highCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean)
-/
@[path]
private lemma sixVertexHorizontalDegreeTwoUnitCharge_of_not_highCharge_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoHallSource T middle hmiddle_pos hmiddle_lt grade}
-- given
  (hdegree : SixVertexLocallyDegreeTwo (sixVertexHorizontalActualDeficitConfigurationPair source).1.1.1 (sixVertexHorizontalActualDeficitConfigurationPair source).1.2.1)
  (hnot : ¬ sixVertexHorizontalDegreeTwoHighCharge source) :
-- imply
  sixVertexHorizontalDegreeTwoUnitCharge source := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalDegreeTwoUnitCharge_of_not_highCharge source hdegree hnot

/--
[sixVertexHorizontalDegreeTwoHighCharge_seed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean)
-/
@[path]
private lemma sixVertexHorizontalDegreeTwoHighCharge_seed_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoHighChargeSources T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  let pair := sixVertexHorizontalActualDeficitConfigurationPair source.1 ∃ hdegree : SixVertexLocallyDegreeTwo pair.1.1.1 pair.1.2.1, ∃ component : (sixVertexDegreeTwoSynchronizedGraph pair.1.1.2.1 pair.1.2.2.1 hdegree).ConnectedComponent, Nonempty (SixVertexDegreeTwoSynchronizedHighChargeSeed pair.1.1.2.1 pair.1.2.2.1 hdegree component) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalDegreeTwoHighCharge_seed source

/--
[SixVertexHorizontalDegreeTwoHighChargeHallRouting.paired_branch_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean)
-/
@[path]
private lemma paired_branch_injective_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle hmiddle_pos hmiddle_lt grade}
  (branch) :
-- imply
  Function.Injective (fun source => routing.paired source branch) := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoHighChargeHallRouting.paired_branch_injective routing

/--
[SixVertexHorizontalDegreeTwoHighChargeHallRouting.paired_inverse_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean)
-/
@[path]
private lemma paired_inverse_spec_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle hmiddle_pos hmiddle_lt grade}
  {output : SixVertexHorizontalDegreeTwoHallTarget T middle hmiddle_pos hmiddle_lt grade}
  {source : {source : SixVertexHorizontalDegreeTwoHighChargeSources T middle hmiddle_pos hmiddle_lt grade // routing.PairedRelated source output}} :
-- imply
  routing.paired source.1 (routing.pairedInverseBranch output source) = output := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoHighChargeHallRouting.paired_inverse_spec routing output source

/--
[SixVertexHorizontalDegreeTwoHighChargeHallRouting.paired_source_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean)
-/
@[path]
private lemma paired_source_degree_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexHorizontalDegreeTwoHighChargeSources T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  2 ≤ (Finset.univ.filter (routing.PairedRelated source)).card := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoHighChargeHallRouting.paired_source_degree routing source

/--
[SixVertexHorizontalDegreeTwoHighChargeHallRouting.paired_inverse_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean)
-/
@[path]
private lemma paired_inverse_degree_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle hmiddle_pos hmiddle_lt grade}
  {target : SixVertexHorizontalDegreeTwoHallTarget T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  (Finset.univ.filter fun source => routing.PairedRelated source target).card ≤ 2 := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoHighChargeHallRouting.paired_inverse_degree routing target

/--
[SixVertexHorizontalDegreeTwoHighChargeHallRouting.paired_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean)
-/
@[path]
private lemma paired_hall_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  ∀ sources : Finset (SixVertexHorizontalDegreeTwoHighChargeSources T middle hmiddle_pos hmiddle_lt grade), sources.card ≤ (Finset.univ.filter fun target => ∃ source, source ∈ sources ∧ routing.PairedRelated source target).card := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoHighChargeHallRouting.paired_hall routing

/--
[SixVertexHorizontalDegreeTwoHighChargeHallRouting.pairedMatching_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean)
-/
@[path]
private lemma pairedMatching_injective_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  Function.Injective routing.pairedMatching := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoHighChargeHallRouting.pairedMatching_injective routing

/--
[SixVertexHorizontalDegreeTwoHighChargeHallRouting.pairedMatching_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean)
-/
@[path]
private lemma pairedMatching_related_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle hmiddle_pos hmiddle_lt grade}
  (source) :
-- imply
  routing.PairedRelated source (routing.pairedMatching source) := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoHighChargeHallRouting.pairedMatching_related routing

/--
[SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean)
-/
@[path]
private lemma reconnect_supported_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle hmiddle_pos hmiddle_lt grade}
  (source) :
-- imply
  sixVertexHorizontalOffDiagonalTwoCycleSupport T middle hmiddle_pos hmiddle_lt grade source (routing.reconnect source) := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect_supported routing

/--
[SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean)
-/
@[path]
private lemma reconnect_injective_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  Function.Injective routing.reconnect := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect_injective routing

/--
[offDiagonalTwoCycleMatching_of_degreeTwoHighChargeHallRoutings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean)
-/
@[path]
private lemma offDiagonalTwoCycleMatching_of_degreeTwoHighChargeHallRoutings_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hroutings : SixVertexHorizontalDegreeTwoHighChargeHallRoutings T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalOffDiagonalTwoCycleMatching T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.offDiagonalTwoCycleMatching_of_degreeTwoHighChargeHallRoutings T middle hmiddle_pos hmiddle_lt hroutings

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoHighChargeHallRoutings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoHighChargeHallRoutings_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hroutings : SixVertexHorizontalDegreeTwoHighChargeHallRoutings T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoHighChargeHallRoutings T middle hmiddle_pos hmiddle_lt hroutings


-- created on 2026-10-23
