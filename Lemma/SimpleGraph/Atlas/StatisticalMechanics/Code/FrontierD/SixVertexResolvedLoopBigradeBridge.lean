import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge
open StatMech StatMech.FrontierD


/--
[sixVertexExplicitResolvedMarkedPairEquivLoopMarked_bigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedLoopBigradeBridge.lean)
-/
@[path]
private lemma sixVertexExplicitResolvedMarkedPairEquivLoopMarked_bigrade_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {k : Nat}
  {resolved : SixVertexExplicitResolvedMarkedPair T left right k} :
-- imply
  sixVertexResolvedLoopMarkedPairBigrade (sixVertexExplicitResolvedMarkedPairEquivLoopMarked T left right k resolved) = sixVertexExplicitResolvedBigrade resolved := by
-- proof
  apply StatMech.FrontierD.sixVertexExplicitResolvedMarkedPairEquivLoopMarked_bigrade resolved

/--
[card_sixVertexExplicitResolvedBigradeFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedLoopBigradeBridge.lean)
-/
@[path]
private lemma card_sixVertexExplicitResolvedBigradeFiber_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {k : Nat}
  {grade : Nat × Nat} :
-- imply
  Fintype.card {resolved : SixVertexExplicitResolvedMarkedPair T left right k // sixVertexExplicitResolvedBigrade resolved = grade} = Fintype.card {loops : SixVertexLoopDecoratedPair T left right // sixVertexLoopDecoratedPairBigrade loops = grade} * grade.1.choose k := by
-- proof
  apply StatMech.FrontierD.card_sixVertexExplicitResolvedBigradeFiber T left right k grade

/--
[resolvedBigradeFibers_of_loopBigradeFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedLoopBigradeBridge.lean)
-/
@[path]
private lemma resolvedBigradeFibers_of_loopBigradeFibers_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (hfiber : SixVertexLoopDecoratedPairBigradeFiberDominates T sourceLeft sourceRight targetLeft targetRight) :
-- imply
  SixVertexExplicitResolvedBigradeFiberDominates T sourceLeft sourceRight targetLeft targetRight := by
-- proof
  apply StatMech.FrontierD.resolvedBigradeFibers_of_loopBigradeFibers hfiber

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_loopBigradeFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedLoopBigradeBridge.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_loopBigradeFibers_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hfiber : SixVertexLoopDecoratedPairBigradeFiberDominates T ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩ middle middle) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_loopBigradeFibers T middle hmiddle_pos hmiddle_lt hfiber


-- created on 2026-10-23
