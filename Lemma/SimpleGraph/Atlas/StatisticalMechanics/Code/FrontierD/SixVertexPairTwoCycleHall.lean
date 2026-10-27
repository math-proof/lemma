import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleHall.Part3
open Finset StatMech StatMech.FrontierD


/--
[SixVertexConfigurationPairTwoCycleFineRelated.totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleHall.lean)
-/
@[path]
private lemma totalC_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
  {source : SixVertexMarkedPairSource T lower upper}
  {target : SixVertexMarkedPairTarget T middle}
-- given
  (hrelated : SixVertexConfigurationPairTwoCycleFineRelated source target) :
-- imply
  sixVertexConfigurationPairTotalC source = sixVertexConfigurationPairTotalC target := by
-- proof
  apply StatMech.FrontierD.SixVertexConfigurationPairTwoCycleFineRelated.totalC hrelated

/--
[configurationPairTwoCycleFineHall_iff_exists_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleHall.lean)
-/
@[path]
private lemma configurationPairTwoCycleFineHall_iff_exists_injective_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)} :
-- imply
  SixVertexConfigurationPairTwoCycleFineHall T lower middle upper <-> exists matching : SixVertexMarkedPairSource T lower upper -> SixVertexMarkedPairTarget T middle, Function.Injective matching /\ forall source, SixVertexConfigurationPairTwoCycleFineRelated source (matching source) := by
-- proof
  apply StatMech.FrontierD.configurationPairTwoCycleFineHall_iff_exists_injective T lower middle upper

/--
[configurationPairTwoCycleFineProfileFiberHall_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleHall.lean)
-/
@[path]
private lemma configurationPairTwoCycleFineProfileFiberHall_iff_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)} :
-- imply
  SixVertexConfigurationPairTwoCycleFineProfileFiberHall T lower middle upper <-> forall profile : SixVertexHorizontalBoundedFineRowProfile T, exists matching : SixVertexConfigurationPairFineProfileFiber T lower upper profile -> SixVertexConfigurationPairFineProfileFiber T middle middle profile, Function.Injective matching /\ forall source, SixVertexConfigurationPairTwoCycleFineProfileRelated source (matching source) := by
-- proof
  apply StatMech.FrontierD.configurationPairTwoCycleFineProfileFiberHall_iff T lower middle upper

/--
[configurationPairTwoCycleFineHall_of_profileFiberHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleHall.lean)
-/
@[path]
private lemma configurationPairTwoCycleFineHall_of_profileFiberHall_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
-- given
  (hFiber : SixVertexConfigurationPairTwoCycleFineProfileFiberHall T lower middle upper) :
-- imply
  SixVertexConfigurationPairTwoCycleFineHall T lower middle upper := by
-- proof
  apply StatMech.FrontierD.configurationPairTwoCycleFineHall_of_profileFiberHall hFiber

/--
[configurationPairTwoCycleFineProfileFiberHall_of_Hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleHall.lean)
-/
@[path]
private lemma configurationPairTwoCycleFineProfileFiberHall_of_Hall_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
-- given
  (hHall : SixVertexConfigurationPairTwoCycleFineHall T lower middle upper) :
-- imply
  SixVertexConfigurationPairTwoCycleFineProfileFiberHall T lower middle upper := by
-- proof
  apply StatMech.FrontierD.configurationPairTwoCycleFineProfileFiberHall_of_Hall hHall

/--
[configurationPairTwoCycleFineHall_iff_profileFiberHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleHall.lean)
-/
@[path]
private lemma configurationPairTwoCycleFineHall_iff_profileFiberHall_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)} :
-- imply
  SixVertexConfigurationPairTwoCycleFineHall T lower middle upper <-> SixVertexConfigurationPairTwoCycleFineProfileFiberHall T lower middle upper := by
-- proof
  apply StatMech.FrontierD.configurationPairTwoCycleFineHall_iff_profileFiberHall T lower middle upper

/--
[configurationPairTotalCReconnection_of_twoCycleFineHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleHall.lean)
-/
@[path]
private lemma configurationPairTotalCReconnection_of_twoCycleFineHall_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
-- given
  (hHall : SixVertexConfigurationPairTwoCycleFineHall T lower middle upper) :
-- imply
  SixVertexConfigurationPairTotalCReconnection T lower middle upper := by
-- proof
  apply StatMech.FrontierD.configurationPairTotalCReconnection_of_twoCycleFineHall hHall

/--
[configurationPairTotalCFibers_of_twoCycleFineHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleHall.lean)
-/
@[path]
private lemma configurationPairTotalCFibers_of_twoCycleFineHall_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
-- given
  (hHall : SixVertexConfigurationPairTwoCycleFineHall T lower middle upper) :
-- imply
  SixVertexConfigurationPairTotalCFiberDominates T lower middle upper := by
-- proof
  apply StatMech.FrontierD.configurationPairTotalCFibers_of_twoCycleFineHall hHall

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_twoCycleFineHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_twoCycleFineHall_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hHall : SixVertexConfigurationPairTwoCycleFineHall T ⟨middle.val - 1, by omega⟩ middle ⟨middle.val + 1, by omega⟩) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_twoCycleFineHall T middle hmiddle_pos hmiddle_lt hHall

/--
[sixVertexSectorTrace_logConcave_of_twoCycleFineHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexSectorTrace_logConcave_of_twoCycleFineHall_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {c : Real}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hc : 2 <= c)
  (hHall : SixVertexConfigurationPairTwoCycleFineHall T ⟨middle.val - 1, by omega⟩ middle ⟨middle.val + 1, by omega⟩) :
-- imply
  Matrix.trace (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) * Matrix.trace (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <= Matrix.trace (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTrace_logConcave_of_twoCycleFineHall T middle hmiddle_pos hmiddle_lt hc hHall


-- created on 2026-10-23
