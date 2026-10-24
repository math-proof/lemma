import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoPositiveEvenAdapter
open StatMech StatMech.FrontierD


/--
[sixVertexFourByTwo_sectorTrace_logConcave_positiveEvenBase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoPositiveEvenAdapter.lean)
-/
@[path]
private lemma sixVertexFourByTwo_sectorTrace_logConcave_positiveEvenBase_eq
  {c : Real}
-- given
  (hc : 2 <= c) :
-- imply
  Matrix.trace (sixVertexSectorTransfer 4 0 c ^ sixVertexPositiveEvenHeight 0) * Matrix.trace (sixVertexSectorTransfer 4 2 c ^ sixVertexPositiveEvenHeight 0) <= Matrix.trace (sixVertexSectorTransfer 4 1 c ^ sixVertexPositiveEvenHeight 0) ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_sectorTrace_logConcave_positiveEvenBase hc


-- created on 2026-10-23
