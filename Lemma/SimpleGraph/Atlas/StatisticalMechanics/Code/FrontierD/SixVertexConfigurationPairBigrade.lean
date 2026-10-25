import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
open StatMech StatMech.FrontierD


/--
[card_sixVertexLoopDecoratedPairBigradeFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairBigrade.lean)
-/
@[path]
private lemma card_sixVertexLoopDecoratedPairBigradeFiber_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {grade : Nat × Nat} :
-- imply
  Fintype.card {decorated : SixVertexLoopDecoratedPair T left right // sixVertexLoopDecoratedPairBigrade decorated = grade} = Fintype.card {pair : SixVertexMarkedSectorConfiguration T left × SixVertexMarkedSectorConfiguration T right // sixVertexConfigurationPairBigrade pair = grade} * 2 ^ grade.1 := by
-- proof
  apply StatMech.FrontierD.card_sixVertexLoopDecoratedPairBigradeFiber T left right grade

/--
[loopBigradeFibers_of_configurationBigradeFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairBigrade.lean)
-/
@[path]
private lemma loopBigradeFibers_of_configurationBigradeFibers_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (hfiber : SixVertexConfigurationPairBigradeFiberDominates T sourceLeft sourceRight targetLeft targetRight) :
-- imply
  SixVertexLoopDecoratedPairBigradeFiberDominates T sourceLeft sourceRight targetLeft targetRight := by
-- proof
  apply StatMech.FrontierD.loopBigradeFibers_of_configurationBigradeFibers hfiber

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_configurationBigradeFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairBigrade.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_configurationBigradeFibers_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hfiber : SixVertexConfigurationPairBigradeFiberDominates T ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩ middle middle) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_configurationBigradeFibers T middle hmiddle_pos hmiddle_lt hfiber


-- created on 2026-10-23
