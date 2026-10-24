import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch
open Finset Matrix Polynomial StatMech StatMech.FrontierD


/--
[SixVertexArrows.weight_eq_pow_cTypeCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalPairedBranch.lean)
-/
@[path]
private lemma weight_eq_pow_cTypeCount_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {c : Real}
-- given
  (homega : omega.IceRule) :
-- imply
  omega.weight c = c ^ sixVertexTorusCTypeCount omega := by
-- proof
  apply StatMech.FrontierD.SixVertexArrows.weight_eq_pow_cTypeCount omega homega c

/--
[sum_pow_sixVertexMarkedSectorConfiguration_eq_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalPairedBranch.lean)
-/
@[path]
private lemma sum_pow_sixVertexMarkedSectorConfiguration_eq_trace_eq
  {T : EvenTorus}
  {sector : Fin (T.width + 1)}
  {c : Real} :
-- imply
  (∑ omega : SixVertexMarkedSectorConfiguration T sector, c ^ sixVertexTorusCTypeCount omega.1) = Matrix.trace (sixVertexSectorTransfer T.width sector.val c ^ T.height) := by
-- proof
  apply StatMech.FrontierD.sum_pow_sixVertexMarkedSectorConfiguration_eq_trace T sector c

/--
[sum_pow_configurationPairTotalC_eq_trace_mul_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalPairedBranch.lean)
-/
@[path]
private lemma sum_pow_configurationPairTotalC_eq_trace_mul_trace_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {c : Real} :
-- imply
  (∑ pair : SixVertexMarkedSectorConfiguration T left × SixVertexMarkedSectorConfiguration T right, c ^ sixVertexConfigurationPairTotalCPhysical pair) = Matrix.trace (sixVertexSectorTransfer T.width left.val c ^ T.height) * Matrix.trace (sixVertexSectorTransfer T.width right.val c ^ T.height) := by
-- proof
  apply StatMech.FrontierD.sum_pow_configurationPairTotalC_eq_trace_mul_trace T left right c

/--
[sixVertexSectorTrace_logConcave_of_physicalPairedBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalPairedBranch.lean)
-/
@[path]
private lemma sixVertexSectorTrace_logConcave_of_physicalPairedBranches_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {c : Real}
  {embeddings : SixVertexConfigurationPhysicalPairedBranchEmbeddings T middle hmiddle_pos hmiddle_lt}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hc : 1 <= c) :
-- imply
  Matrix.trace (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) * Matrix.trace (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <= Matrix.trace (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTrace_logConcave_of_physicalPairedBranches T middle hmiddle_pos hmiddle_lt hc embeddings


-- created on 2026-10-23
