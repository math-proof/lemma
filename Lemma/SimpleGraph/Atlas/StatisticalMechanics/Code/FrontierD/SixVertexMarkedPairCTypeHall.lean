import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall
open Finset Matrix Polynomial StatMech StatMech.FrontierD


/--
[exists_injective_gradePreserving_iff_fiberCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean)
-/
@[path]
private lemma exists_injective_gradePreserving_iff_fiberCard_eq
  [Fintype Source]
  [Fintype Target]
  [DecidableEq Grade]
-- given
  (sourceGrade : Source -> Grade)
  (targetGrade : Target -> Grade) :
-- imply
  (exists matching : Source -> Target, Function.Injective matching /\ forall source, sourceGrade source = targetGrade (matching source)) <-> forall grade : Grade, Fintype.card {source : Source // sourceGrade source = grade} <= Fintype.card {target : Target // targetGrade target = grade} := by
-- proof
  apply StatMech.FrontierD.exists_injective_gradePreserving_iff_fiberCard sourceGrade targetGrade

/--
[exists_injective_bigradePreserving_iff_fiberCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean)
-/
@[path]
private lemma exists_injective_bigradePreserving_iff_fiberCard_eq
  [Fintype Source]
  [Fintype Target]
-- given
  (sourceGrade : Source -> Nat × Nat)
  (targetGrade : Target -> Nat × Nat) :
-- imply
  (exists matching : Source -> Target, Function.Injective matching /\ forall source, sourceGrade source = targetGrade (matching source)) <-> forall grade : Nat × Nat, Fintype.card {source : Source // sourceGrade source = grade} <= Fintype.card {target : Target // targetGrade target = grade} := by
-- proof
  apply StatMech.FrontierD.exists_injective_bigradePreserving_iff_fiberCard sourceGrade targetGrade

/--
[sixVertexMarkedPairMultiplicityNat_eq_of_totalC_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean)
-/
@[path]
private lemma sixVertexMarkedPairMultiplicityNat_eq_of_totalC_eq_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {pair : SixVertexMarkedSectorConfiguration T left × SixVertexMarkedSectorConfiguration T right}
  {k total : Nat}
-- given
  (htotal : sixVertexConfigurationPairTotalC pair = total) :
-- imply
  sixVertexMarkedPairMultiplicityNat pair.1.1 pair.2.1 k = 2 ^ (total - k) * total.choose k := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedPairMultiplicityNat_eq_of_totalC_eq pair k total htotal

/--
[sixVertexMarkedDecoratedPairTotalC_eq_pairTotalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean)
-/
@[path]
private lemma sixVertexMarkedDecoratedPairTotalC_eq_pairTotalC_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {k : Nat}
  {pair : SixVertexMarkedDecoratedPair T left right k} :
-- imply
  sixVertexMarkedDecoratedPairTotalC pair = sixVertexConfigurationPairTotalC pair.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedDecoratedPairTotalC_eq_pairTotalC pair

/--
[card_sixVertexMarkedDecoratedPairTotalCFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean)
-/
@[path]
private lemma card_sixVertexMarkedDecoratedPairTotalCFiber_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {k total : Nat} :
-- imply
  Fintype.card {decorated : SixVertexMarkedDecoratedPair T left right k // sixVertexMarkedDecoratedPairTotalC decorated = total} = Fintype.card {pair : SixVertexMarkedSectorConfiguration T left × SixVertexMarkedSectorConfiguration T right // sixVertexConfigurationPairTotalC pair = total} * (2 ^ (total - k) * total.choose k) := by
-- proof
  apply StatMech.FrontierD.card_sixVertexMarkedDecoratedPairTotalCFiber T left right k total

/--
[configurationPairTotalCReconnection_iff_fiberDominates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean)
-/
@[path]
private lemma configurationPairTotalCReconnection_iff_fiberDominates_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)} :
-- imply
  SixVertexConfigurationPairTotalCReconnection T lower middle upper <-> SixVertexConfigurationPairTotalCFiberDominates T lower middle upper := by
-- proof
  apply StatMech.FrontierD.configurationPairTotalCReconnection_iff_fiberDominates T lower middle upper

/--
[decoratedTotalCFiberDominates_of_configurationPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean)
-/
@[path]
private lemma decoratedTotalCFiberDominates_of_configurationPair_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
  {k : Nat}
-- given
  (hfiber : SixVertexConfigurationPairTotalCFiberDominates T lower middle upper) :
-- imply
  SixVertexMarkedDecoratedPairTotalCFiberDominates T lower middle upper k := by
-- proof
  apply StatMech.FrontierD.decoratedTotalCFiberDominates_of_configurationPair hfiber k

/--
[exists_injective_equalTotalC_of_fiberDominates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean)
-/
@[path]
private lemma exists_injective_equalTotalC_of_fiberDominates_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
  {k : Nat}
-- given
  (hfiber : SixVertexMarkedDecoratedPairTotalCFiberDominates T lower middle upper k) :
-- imply
  exists matching : SixVertexMarkedDecoratedPair T lower upper k -> SixVertexMarkedDecoratedPair T middle middle k, Function.Injective matching /\ forall source, SixVertexMarkedDecoratedPairEqualTotalC source (matching source) := by
-- proof
  apply StatMech.FrontierD.exists_injective_equalTotalC_of_fiberDominates hfiber

/--
[sixVertexMarkedDecoratedPairHall_equalTotalC_of_fiberDominates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean)
-/
@[path]
private lemma sixVertexMarkedDecoratedPairHall_equalTotalC_of_fiberDominates_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
  {k : Nat}
-- given
  (hfiber : SixVertexMarkedDecoratedPairTotalCFiberDominates T lower middle upper k) :
-- imply
  SixVertexMarkedDecoratedPairHall T lower middle upper k SixVertexMarkedDecoratedPairEqualTotalC := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedDecoratedPairHall_equalTotalC_of_fiberDominates hfiber

/--
[sixVertexMarkedDecoratedPairHall_equalTotalC_of_configurationPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean)
-/
@[path]
private lemma sixVertexMarkedDecoratedPairHall_equalTotalC_of_configurationPair_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
  {k : Nat}
-- given
  (hfiber : SixVertexConfigurationPairTotalCFiberDominates T lower middle upper) :
-- imply
  SixVertexMarkedDecoratedPairHall T lower middle upper k SixVertexMarkedDecoratedPairEqualTotalC := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedDecoratedPairHall_equalTotalC_of_configurationPair hfiber k

/--
[sixVertexMarkedDecoratedPairHall_equalTotalC_of_reconnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean)
-/
@[path]
private lemma sixVertexMarkedDecoratedPairHall_equalTotalC_of_reconnection_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
  {k : Nat}
-- given
  (hreconnect : SixVertexConfigurationPairTotalCReconnection T lower middle upper) :
-- imply
  SixVertexMarkedDecoratedPairHall T lower middle upper k SixVertexMarkedDecoratedPairEqualTotalC := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedDecoratedPairHall_equalTotalC_of_reconnection hreconnect k

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCFibers_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hfiber : SixVertexConfigurationPairTotalCFiberDominates T ⟨middle.val - 1, by omega⟩ middle ⟨middle.val + 1, by omega⟩) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCFibers T middle hmiddle_pos hmiddle_lt hfiber

/--
[sixVertexSectorTrace_logConcave_of_totalCFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean)
-/
@[path]
private lemma sixVertexSectorTrace_logConcave_of_totalCFibers_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {c : Real}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hc : 2 <= c)
  (hfiber : SixVertexConfigurationPairTotalCFiberDominates T ⟨middle.val - 1, by omega⟩ middle ⟨middle.val + 1, by omega⟩) :
-- imply
  Matrix.trace (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) * Matrix.trace (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <= Matrix.trace (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTrace_logConcave_of_totalCFibers T middle hmiddle_pos hmiddle_lt hc hfiber

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCReconnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCReconnection_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hreconnect : SixVertexConfigurationPairTotalCReconnection T ⟨middle.val - 1, by omega⟩ middle ⟨middle.val + 1, by omega⟩) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCReconnection T middle hmiddle_pos hmiddle_lt hreconnect

/--
[sixVertexMarkedDecoratedPairHall_equalTotalC_iff_fiberDominates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean)
-/
@[path]
private lemma sixVertexMarkedDecoratedPairHall_equalTotalC_iff_fiberDominates_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
  {k : Nat} :
-- imply
  SixVertexMarkedDecoratedPairHall T lower middle upper k SixVertexMarkedDecoratedPairEqualTotalC <-> SixVertexMarkedDecoratedPairTotalCFiberDominates T lower middle upper k := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedDecoratedPairHall_equalTotalC_iff_fiberDominates T lower middle upper k

/--
[sixVertexFourByTwo_reconnection_equalTotalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean)
-/
@[path]
private lemma sixVertexFourByTwo_reconnection_equalTotalC_eq :
-- imply
  sixVertexTorusCTypeCount sixVertexFourByTwoLowArrows + sixVertexTorusCTypeCount sixVertexFourByTwoHighArrows = sixVertexTorusCTypeCount sixVertexFourByTwoMiddleArrows + sixVertexTorusCTypeCount sixVertexFourByTwoMiddleArrows := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_reconnection_equalTotalC


-- created on 2026-10-23
