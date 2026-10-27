import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileAggregate.Part2
open Finset StatMech StatMech.FrontierD


/--
[card_sixVertexHorizontalActualDeficitRowProfileFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileAggregate.lean)
-/
@[path]
private lemma card_sixVertexHorizontalActualDeficitRowProfileFiber_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
  {rowProfile : SixVertexHorizontalRowZeroProfile T} :
-- imply
  Fintype.card {source : SixVertexHorizontalActualDeficitTokens T grade sourceLeft sourceRight targetLeft targetRight // sixVertexHorizontalActualDeficitRowProfile source = rowProfile} = ∑ horizontal : SixVertexHorizontalPairRowBigradeFiber T grade rowProfile, sixVertexHorizontalProfileDeficit sourceLeft sourceRight targetLeft targetRight (sixVertexHorizontalPairCompletionProfile T horizontal.1) := by
-- proof
  apply StatMech.FrontierD.card_sixVertexHorizontalActualDeficitRowProfileFiber T grade sourceLeft sourceRight targetLeft targetRight rowProfile

/--
[card_sixVertexHorizontalActualSurplusRowProfileFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileAggregate.lean)
-/
@[path]
private lemma card_sixVertexHorizontalActualSurplusRowProfileFiber_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
  {rowProfile : SixVertexHorizontalRowZeroProfile T} :
-- imply
  Fintype.card {target : SixVertexHorizontalActualSurplusTokens T grade sourceLeft sourceRight targetLeft targetRight // sixVertexHorizontalActualSurplusRowProfile target = rowProfile} = ∑ horizontal : SixVertexHorizontalPairRowBigradeFiber T grade rowProfile, sixVertexHorizontalProfileSurplus sourceLeft sourceRight targetLeft targetRight (sixVertexHorizontalPairCompletionProfile T horizontal.1) := by
-- proof
  apply StatMech.FrontierD.card_sixVertexHorizontalActualSurplusRowProfileFiber T grade sourceLeft sourceRight targetLeft targetRight rowProfile

/--
[rowProfileResidualCapacity_iff_signedNonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileAggregate.lean)
-/
@[path]
private lemma rowProfileResidualCapacity_iff_signedNonnegative_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)} :
-- imply
  SixVertexHorizontalRowProfileResidualCapacity T sourceLeft sourceRight targetLeft targetRight <-> SixVertexHorizontalRowProfileAggregateSignedNonnegative T sourceLeft sourceRight targetLeft targetRight := by
-- proof
  apply StatMech.FrontierD.rowProfileResidualCapacity_iff_signedNonnegative T sourceLeft sourceRight targetLeft targetRight

/--
[configurationBigradeFibers_of_rowProfileSignedNonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileAggregate.lean)
-/
@[path]
private lemma configurationBigradeFibers_of_rowProfileSignedNonnegative_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (hsigned : SixVertexHorizontalRowProfileAggregateSignedNonnegative T sourceLeft sourceRight targetLeft targetRight) :
-- imply
  SixVertexConfigurationPairBigradeFiberDominates T sourceLeft sourceRight targetLeft targetRight := by
-- proof
  apply StatMech.FrontierD.configurationBigradeFibers_of_rowProfileSignedNonnegative T sourceLeft sourceRight targetLeft targetRight hsigned

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_rowProfileSigned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileAggregate.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_rowProfileSigned_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hsigned : SixVertexHorizontalRowProfileAggregateSignedNonnegative T ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩ middle middle) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_rowProfileSigned T middle hmiddle_pos hmiddle_lt hsigned


-- created on 2026-10-23
