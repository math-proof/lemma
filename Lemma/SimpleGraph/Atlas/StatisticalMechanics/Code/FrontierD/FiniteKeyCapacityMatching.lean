import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteKeyCapacityMatching.Part3
open Finset StatMech StatMech.FrontierD


/--
[sigmaFinFiberCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteKeyCapacityMatching.lean)
-/
@[path]
private lemma sigmaFinFiberCard_eq
  [Fintype Key]
  [DecidableEq Key]
  {key : Key}
-- given
  (capacity : Key -> Nat) :
-- imply
  Fintype.card {source : FiniteKeyCapacityCopies Key capacity // source.1 = key} = capacity key := by
-- proof
  apply StatMech.FrontierD.sigmaFinFiberCard capacity key

/--
[finiteKeyCapacityCopiesEquiv_key](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteKeyCapacityMatching.lean)
-/
@[path]
private lemma finiteKeyCapacityCopiesEquiv_key_eq
  [Fintype Source]
  [Fintype Key]
  [DecidableEq Key]
  {source : Source}
-- given
  (keyOf : Source -> Key) :
-- imply
  (finiteKeyCapacityCopiesEquiv keyOf source).1 = keyOf source := by
-- proof
  apply StatMech.FrontierD.finiteKeyCapacityCopiesEquiv_key keyOf source

/--
[finiteKeyCapacityCopiesEquiv_symm_key](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteKeyCapacityMatching.lean)
-/
@[path]
private lemma finiteKeyCapacityCopiesEquiv_symm_key_eq
  [Fintype Source]
  [Fintype Key]
  [DecidableEq Key]
-- given
  (keyOf : Source -> Key)
  (copy : FiniteKeyCapacityCopies Key (fun key => Fintype.card {source : Source // keyOf source = key})) :
-- imply
  keyOf ((finiteKeyCapacityCopiesEquiv keyOf).symm copy) = copy.1 := by
-- proof
  apply StatMech.FrontierD.finiteKeyCapacityCopiesEquiv_symm_key keyOf copy

/--
[finiteKeyExpandedMatching_of_supportedMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteKeyCapacityMatching.lean)
-/
@[path]
private lemma finiteKeyExpandedMatching_of_supportedMatching_eq
  [Fintype Source]
  [Fintype Target]
  [Fintype Key]
  [DecidableEq Key]
-- given
  (sourceKey : Source -> Key)
  (targetKey : Target -> Key)
  (related : Key -> Key -> Prop)
  (matching : Source -> Target)
  (hinjective : Function.Injective matching)
  (hsupported : forall source, related (sourceKey source) (targetKey (matching source))) :
-- imply
  exists copiedMatching : FiniteKeyCapacityCopies Key (fun key => Fintype.card {source : Source // sourceKey source = key}) -> FiniteKeyCapacityCopies Key (fun key => Fintype.card {target : Target // targetKey target = key}), Function.Injective copiedMatching ∧ forall source, related source.1 (copiedMatching source).1 := by
-- proof
  apply StatMech.FrontierD.finiteKeyExpandedMatching_of_supportedMatching sourceKey targetKey related matching hinjective hsupported

/--
[finiteKeyCapacityHall_iff_exists_expandedMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteKeyCapacityMatching.lean)
-/
@[path]
private lemma finiteKeyCapacityHall_iff_exists_expandedMatching_eq
  [Fintype Key]
  [DecidableEq Key]
  [DecidableRel related]
-- given
  (sourceCapacity targetCapacity : Key -> Nat)
  (related : Key -> Key -> Prop) :
-- imply
  (forall sourceKeys : Finset Key, (∑ key ∈ sourceKeys, sourceCapacity key) <= ∑ key ∈ (Finset.univ.filter fun targetKey => exists sourceKey, sourceKey ∈ sourceKeys ∧ related sourceKey targetKey), targetCapacity key) <-> exists matching : FiniteKeyCapacityCopies Key sourceCapacity -> FiniteKeyCapacityCopies Key targetCapacity, Function.Injective matching ∧ forall source, related source.1 (matching source).1 := by
-- proof
  apply StatMech.FrontierD.finiteKeyCapacityHall_iff_exists_expandedMatching sourceCapacity targetCapacity related

/--
[twoCycleExpandedCapacityMatchings_of_offDiagonalMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteKeyCapacityMatching.lean)
-/
@[path]
private lemma twoCycleExpandedCapacityMatchings_of_offDiagonalMatching_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hmatching : SixVertexHorizontalOffDiagonalTwoCycleMatching T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalTwoCycleExpandedCapacityMatchings T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.twoCycleExpandedCapacityMatchings_of_offDiagonalMatching T middle hmiddle_pos hmiddle_lt hmatching

/--
[twoCycleKeyCapacityHall_iff_expandedCapacityMatchings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteKeyCapacityMatching.lean)
-/
@[path]
private lemma twoCycleKeyCapacityHall_iff_expandedCapacityMatchings_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  SixVertexHorizontalTwoCycleKeyCapacityHall T middle hmiddle_pos hmiddle_lt <-> SixVertexHorizontalTwoCycleExpandedCapacityMatchings T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.twoCycleKeyCapacityHall_iff_expandedCapacityMatchings T middle hmiddle_pos hmiddle_lt

/--
[offDiagonalTwoCycleMatching_iff_expandedCapacityMatchings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteKeyCapacityMatching.lean)
-/
@[path]
private lemma offDiagonalTwoCycleMatching_iff_expandedCapacityMatchings_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  SixVertexHorizontalOffDiagonalTwoCycleMatching T middle hmiddle_pos hmiddle_lt <-> SixVertexHorizontalTwoCycleExpandedCapacityMatchings T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.offDiagonalTwoCycleMatching_iff_expandedCapacityMatchings T middle hmiddle_pos hmiddle_lt

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_expandedCapacityMatchings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteKeyCapacityMatching.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_expandedCapacityMatchings_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hmatching : SixVertexHorizontalTwoCycleExpandedCapacityMatchings T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_expandedCapacityMatchings T middle hmiddle_pos hmiddle_lt hmatching

/--
[sixVertexSectorTrace_logConcave_of_expandedCapacityMatchings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteKeyCapacityMatching.lean)
-/
@[path]
private lemma sixVertexSectorTrace_logConcave_of_expandedCapacityMatchings_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {c : Real}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hc : 2 <= c)
  (hmatching : SixVertexHorizontalTwoCycleExpandedCapacityMatchings T middle hmiddle_pos hmiddle_lt) :
-- imply
  Matrix.trace (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) * Matrix.trace (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <= Matrix.trace (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTrace_logConcave_of_expandedCapacityMatchings T middle hmiddle_pos hmiddle_lt hc hmatching


-- created on 2026-10-23
