import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationCumulativePairedBranch
open StatMech StatMech.FrontierD


/--
[SixVertexConfigurationCumulativePairedBranchEmbeddings.upperCumulative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationCumulativePairedBranch.lean)
-/
@[path]
private lemma upperCumulative_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {embeddings : SixVertexConfigurationCumulativePairedBranchEmbeddings T middle hmiddle_pos hmiddle_lt} :
-- imply
  ∀ totalC, (Finset.univ.filter fun pair : SixVertexConfigurationCumulativeSource T middle hmiddle_pos hmiddle_lt => totalC ≤ sixVertexConfigurationCumulativeTotalC pair).card ≤ (Finset.univ.filter fun pair : SixVertexConfigurationCumulativeTarget T middle => totalC ≤ sixVertexConfigurationCumulativeTotalC pair).card := by
-- proof
  apply StatMech.FrontierD.SixVertexConfigurationCumulativePairedBranchEmbeddings.upperCumulative embeddings

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_cumulativePairedBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationCumulativePairedBranch.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_cumulativePairedBranches_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {embeddings : SixVertexConfigurationCumulativePairedBranchEmbeddings T middle hmiddle_pos hmiddle_lt}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_cumulativePairedBranches T middle hmiddle_pos hmiddle_lt embeddings


-- created on 2026-10-23
