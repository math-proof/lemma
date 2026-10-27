import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall.Part4
open Finset StatMech StatMech.FrontierD


/--
[finiteRelationHall_of_keyCapacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean)
-/
@[path]
private lemma finiteRelationHall_of_keyCapacity_eq
  [Fintype Source]
  [Fintype Target]
  [Fintype Key]
  [DecidableEq Source]
  [DecidableEq Target]
  [DecidableEq Key]
  [DecidableRel keyRelated]
  [DecidableRel related]
-- given
  (sourceKey : Source -> Key)
  (targetKey : Target -> Key)
  (keyRelated : Key -> Key -> Prop)
  (related : Source -> Target -> Prop)
  (hsound : forall source target, keyRelated (sourceKey source) (targetKey target) -> related source target)
  (hcapacity : forall sourceKeys : Finset Key, (∑ key ∈ sourceKeys, Fintype.card {source : Source // sourceKey source = key}) <= ∑ key ∈ (Finset.univ.filter fun targetKeyValue => exists sourceKeyValue, sourceKeyValue ∈ sourceKeys ∧ keyRelated sourceKeyValue targetKeyValue), Fintype.card {target : Target // targetKey target = key}) :
-- imply
  forall sources : Finset Source, sources.card <= (Finset.univ.filter fun target => exists source, source ∈ sources ∧ related source target).card := by
-- proof
  apply StatMech.FrontierD.finiteRelationHall_of_keyCapacity sourceKey targetKey keyRelated related hsound hcapacity

/--
[FiniteKeyCapacityTransport.hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean)
-/
@[path]
private lemma hall_eq
  [Fintype Key]
  [DecidableEq Key]
  {sourceCapacity targetCapacity : Key -> Nat}
  {related : Key -> Key -> Prop}
  [DecidableRel related]
  {transport : FiniteKeyCapacityTransport Key sourceCapacity targetCapacity related} :
-- imply
  forall sourceKeys : Finset Key, (∑ key ∈ sourceKeys, sourceCapacity key) <= ∑ key ∈ (Finset.univ.filter fun targetKey => exists sourceKey, sourceKey ∈ sourceKeys ∧ related sourceKey targetKey), targetCapacity key := by
-- proof
  apply StatMech.FrontierD.FiniteKeyCapacityTransport.hall transport

/--
[finiteKeyCapacityHall_of_injectiveRouting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean)
-/
@[path]
private lemma finiteKeyCapacityHall_of_injectiveRouting_eq
  [Fintype Key]
  [DecidableEq Key]
  [DecidableRel related]
-- given
  (sourceCapacity targetCapacity : Key -> Nat)
  (related : Key -> Key -> Prop)
  (route : Key -> Key)
  (hinjective : Function.Injective route)
  (hsupported : forall key, related key (route key))
  (hcapacity : forall key, sourceCapacity key <= targetCapacity (route key)) :
-- imply
  forall sourceKeys : Finset Key, (∑ key ∈ sourceKeys, sourceCapacity key) <= ∑ key ∈ (Finset.univ.filter fun targetKey => exists sourceKey, sourceKey ∈ sourceKeys ∧ related sourceKey targetKey), targetCapacity key := by
-- proof
  apply StatMech.FrontierD.finiteKeyCapacityHall_of_injectiveRouting sourceCapacity targetCapacity related route hinjective hsupported hcapacity

/--
[sixVertexPairFineUnionKeyTwoCycleRelated_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean)
-/
@[path]
private lemma sixVertexPairFineUnionKeyTwoCycleRelated_refl_eq
  {T : EvenTorus}
  {key : SixVertexPairFineUnionKey T} :
-- imply
  SixVertexPairFineUnionKeyTwoCycleRelated key key := by
-- proof
  apply StatMech.FrontierD.sixVertexPairFineUnionKeyTwoCycleRelated_refl key

/--
[sixVertexPairFineUnionKeyTwoCycleRelated_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean)
-/
@[path]
private lemma sixVertexPairFineUnionKeyTwoCycleRelated_symm_eq
  {T : EvenTorus}
  {source target : SixVertexPairFineUnionKey T}
-- given
  (hrelated : SixVertexPairFineUnionKeyTwoCycleRelated source target) :
-- imply
  SixVertexPairFineUnionKeyTwoCycleRelated target source := by
-- proof
  apply StatMech.FrontierD.sixVertexPairFineUnionKeyTwoCycleRelated_symm hrelated

/--
[sixVertexPairFineUnionKeyTwoCycleRelated_sound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean)
-/
@[path]
private lemma sixVertexPairFineUnionKeyTwoCycleRelated_sound_eq
  {T : EvenTorus}
  {source target : SixVertexArrows T × SixVertexArrows T}
-- given
  (hrelated : SixVertexPairFineUnionKeyTwoCycleRelated (sixVertexPairFineUnionKey source) (sixVertexPairFineUnionKey target)) :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated source target := by
-- proof
  apply StatMech.FrontierD.sixVertexPairFineUnionKeyTwoCycleRelated_sound hrelated

/--
[sixVertexPairFineUnionKeyTwoCycleRelated_complete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean)
-/
@[path]
private lemma sixVertexPairFineUnionKeyTwoCycleRelated_complete_eq
  {T : EvenTorus}
  {source target : SixVertexArrows T × SixVertexArrows T}
-- given
  (hrelated : sixVertexPairAtMostTwoCycleFineRelated source target) :
-- imply
  SixVertexPairFineUnionKeyTwoCycleRelated (sixVertexPairFineUnionKey source) (sixVertexPairFineUnionKey target) := by
-- proof
  apply StatMech.FrontierD.sixVertexPairFineUnionKeyTwoCycleRelated_complete hrelated

/--
[twoCycleKeyCapacityHall_of_injectiveKeyRoutings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean)
-/
@[path]
private lemma twoCycleKeyCapacityHall_of_injectiveKeyRoutings_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hrouting : SixVertexHorizontalTwoCycleInjectiveKeyRoutings T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalTwoCycleKeyCapacityHall T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.twoCycleKeyCapacityHall_of_injectiveKeyRoutings T middle hmiddle_pos hmiddle_lt hrouting

/--
[twoCycleKeyCapacityHall_of_transports](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean)
-/
@[path]
private lemma twoCycleKeyCapacityHall_of_transports_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (htransports : SixVertexHorizontalTwoCycleKeyCapacityTransports T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalTwoCycleKeyCapacityHall T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.twoCycleKeyCapacityHall_of_transports T middle hmiddle_pos hmiddle_lt htransports

/--
[actualDeficitTokenHall_of_twoCycleKeyCapacityHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean)
-/
@[path]
private lemma actualDeficitTokenHall_of_twoCycleKeyCapacityHall_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hcapacity : SixVertexHorizontalTwoCycleKeyCapacityHall T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalActualDeficitTokenHall T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle (sixVertexHorizontalOffDiagonalTwoCycleSupport T middle hmiddle_pos hmiddle_lt) := by
-- proof
  apply StatMech.FrontierD.actualDeficitTokenHall_of_twoCycleKeyCapacityHall T middle hmiddle_pos hmiddle_lt hcapacity

/--
[offDiagonalTwoCycleMatching_of_keyCapacityHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean)
-/
@[path]
private lemma offDiagonalTwoCycleMatching_of_keyCapacityHall_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hcapacity : SixVertexHorizontalTwoCycleKeyCapacityHall T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalOffDiagonalTwoCycleMatching T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.offDiagonalTwoCycleMatching_of_keyCapacityHall T middle hmiddle_pos hmiddle_lt hcapacity

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_keyCapacityHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_keyCapacityHall_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hcapacity : SixVertexHorizontalTwoCycleKeyCapacityHall T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_keyCapacityHall T middle hmiddle_pos hmiddle_lt hcapacity

/--
[sixVertexSectorTrace_logConcave_of_keyCapacityHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean)
-/
@[path]
private lemma sixVertexSectorTrace_logConcave_of_keyCapacityHall_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {c : Real}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hc : 2 <= c)
  (hcapacity : SixVertexHorizontalTwoCycleKeyCapacityHall T middle hmiddle_pos hmiddle_lt) :
-- imply
  Matrix.trace (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) * Matrix.trace (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <= Matrix.trace (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTrace_logConcave_of_keyCapacityHall T middle hmiddle_pos hmiddle_lt hc hcapacity

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_keyCapacityTransports](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_keyCapacityTransports_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (htransports : SixVertexHorizontalTwoCycleKeyCapacityTransports T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_keyCapacityTransports T middle hmiddle_pos hmiddle_lt htransports

/--
[sixVertexSectorTrace_logConcave_of_keyCapacityTransports](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean)
-/
@[path]
private lemma sixVertexSectorTrace_logConcave_of_keyCapacityTransports_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {c : Real}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hc : 2 <= c)
  (htransports : SixVertexHorizontalTwoCycleKeyCapacityTransports T middle hmiddle_pos hmiddle_lt) :
-- imply
  Matrix.trace (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) * Matrix.trace (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <= Matrix.trace (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTrace_logConcave_of_keyCapacityTransports T middle hmiddle_pos hmiddle_lt hc htransports


-- created on 2026-10-23
