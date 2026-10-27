import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairTotalCMonotone.Part2
open Finset Matrix Polynomial StatMech StatMech.FrontierD


/--
[markedDecorationMultiplicity_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairTotalCMonotone.lean)
-/
@[path]
private lemma markedDecorationMultiplicity_mono_eq
  {sourceTotal targetTotal k : Nat}
-- given
  (htotal : sourceTotal <= targetTotal) :
-- imply
  2 ^ (sourceTotal - k) * sourceTotal.choose k <= 2 ^ (targetTotal - k) * targetTotal.choose k := by
-- proof
  apply StatMech.FrontierD.markedDecorationMultiplicity_mono htotal

/--
[sixVertexMarkedPairMultiplicityNat_mono_of_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairTotalCMonotone.lean)
-/
@[path]
private lemma sixVertexMarkedPairMultiplicityNat_mono_of_totalC_eq
  {T : EvenTorus}
  {omega eta alpha beta : SixVertexArrows T}
  {k : Nat}
-- given
  (htotal : sixVertexTorusCTypeCount omega + sixVertexTorusCTypeCount eta <= sixVertexTorusCTypeCount alpha + sixVertexTorusCTypeCount beta) :
-- imply
  sixVertexMarkedPairMultiplicityNat omega eta k <= sixVertexMarkedPairMultiplicityNat alpha beta k := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedPairMultiplicityNat_mono_of_totalC htotal

/--
[sixVertexMarkedSectorPairMass_le_of_totalCEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairTotalCMonotone.lean)
-/
@[path]
private lemma sixVertexMarkedSectorPairMass_le_of_totalCEmbedding_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
  {k : Nat}
  {base : (SixVertexMarkedSectorConfiguration T lower × SixVertexMarkedSectorConfiguration T upper) ↪ (SixVertexMarkedSectorConfiguration T middle × SixVertexMarkedSectorConfiguration T middle)}
-- given
  (htotal : forall pair, sixVertexTorusCTypeCount pair.1.1 + sixVertexTorusCTypeCount pair.2.1 <= sixVertexTorusCTypeCount (base pair).1.1 + sixVertexTorusCTypeCount (base pair).2.1) :
-- imply
  sixVertexMarkedSectorPairMass T lower upper k <= sixVertexMarkedSectorPairMass T middle middle k := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedSectorPairMass_le_of_totalCEmbedding T lower middle upper k base htotal

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairTotalCMonotone.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCEmbedding_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {base : (SixVertexMarkedSectorConfiguration T ⟨middle.val - 1, by omega⟩ × SixVertexMarkedSectorConfiguration T ⟨middle.val + 1, by omega⟩) ↪ (SixVertexMarkedSectorConfiguration T middle × SixVertexMarkedSectorConfiguration T middle)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (htotal : forall pair, sixVertexTorusCTypeCount pair.1.1 + sixVertexTorusCTypeCount pair.2.1 <= sixVertexTorusCTypeCount (base pair).1.1 + sixVertexTorusCTypeCount (base pair).2.1) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCEmbedding T middle hmiddle_pos hmiddle_lt base htotal


-- created on 2026-10-23
