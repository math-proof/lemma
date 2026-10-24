import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourCentralTrace
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexSectorTrace_particleHole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourCentralTrace.lean)
-/
@[path]
private lemma sixVertexSectorTrace_particleHole_eq
  {N n : Nat}
  {M : Nat}
  {c : Real}
-- given
  (hn : n <= N) :
-- imply
  Matrix.trace (sixVertexSectorTransfer N (N - n) c ^ M) = Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTrace_particleHole hn M c

/--
[sixVertexFourByFour_sectorTrace_logConcave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourCentralTrace.lean)
-/
@[path]
private lemma sixVertexFourByFour_sectorTrace_logConcave_eq
  {n : Nat}
  {c : Real}
-- given
  (hn0 : 0 < n)
  (hn4 : n < 4)
  (hc : 1 <= c) :
-- imply
  Matrix.trace (sixVertexSectorTransfer 4 (n - 1) c ^ 4) * Matrix.trace (sixVertexSectorTransfer 4 (n + 1) c ^ 4) <= Matrix.trace (sixVertexSectorTransfer 4 n c ^ 4) ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFour_sectorTrace_logConcave n hn0 hn4 hc

/--
[sixVertexFourByFour_sectorTrace_le_central](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourCentralTrace.lean)
-/
@[path]
private lemma sixVertexFourByFour_sectorTrace_le_central_eq
  {n : Nat}
  {c : Real}
-- given
  (hn : n <= 4)
  (hc : 1 <= c) :
-- imply
  Matrix.trace (sixVertexSectorTransfer 4 n c ^ 4) <= Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 4) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFour_sectorTrace_le_central n hn hc

/--
[sixVertexFourByFour_centralTrace_le_fixedWidthPartitionSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourCentralTrace.lean)
-/
@[path]
private lemma sixVertexFourByFour_centralTrace_le_fixedWidthPartitionSum_eq
  {c : Real}
-- given
  (hc : 0 < c) :
-- imply
  Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 4) <= sixVertexFixedWidthPartitionSum 4 4 c := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFour_centralTrace_le_fixedWidthPartitionSum hc

/--
[sixVertexFourByFour_fixedWidthPartitionSum_le_five_mul_centralTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourCentralTrace.lean)
-/
@[path]
private lemma sixVertexFourByFour_fixedWidthPartitionSum_le_five_mul_centralTrace_eq
  {c : Real}
-- given
  (hc : 1 <= c) :
-- imply
  sixVertexFixedWidthPartitionSum 4 4 c <= 5 * Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 4) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFour_fixedWidthPartitionSum_le_five_mul_centralTrace hc

/--
[sixVertexFourByFour_logPressureGap_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourCentralTrace.lean)
-/
@[path]
private lemma sixVertexFourByFour_logPressureGap_mem_Icc_eq
  {c : Real}
-- given
  (hc : 1 <= c) :
-- imply
  0 <= Real.log (sixVertexFixedWidthPartitionSum 4 4 c) - Real.log (Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 4)) ∧ Real.log (sixVertexFixedWidthPartitionSum 4 4 c) - Real.log (Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 4)) <= Real.log 5 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFour_logPressureGap_mem_Icc hc

/--
[sixVertexFourByFour_pressureDensityGap_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourCentralTrace.lean)
-/
@[path]
private lemma sixVertexFourByFour_pressureDensityGap_mem_Icc_eq
  {c : Real}
-- given
  (hc : 1 <= c) :
-- imply
  0 <= (Real.log (sixVertexFixedWidthPartitionSum 4 4 c) - Real.log (Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 4))) / 16 ∧ (Real.log (sixVertexFixedWidthPartitionSum 4 4 c) - Real.log (Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 4))) / 16 <= Real.log 5 / 16 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFour_pressureDensityGap_mem_Icc hc

/--
[sixVertexFourByFour_balancedTraceShare_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourCentralTrace.lean)
-/
@[path]
private lemma sixVertexFourByFour_balancedTraceShare_mem_Icc_eq
  {c : Real}
-- given
  (hc : 1 <= c) :
-- imply
  (1 : Real) / 5 <= sixVertexBalancedTraceShare 4 4 c ∧ sixVertexBalancedTraceShare 4 4 c <= 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFour_balancedTraceShare_mem_Icc hc

/--
[fkQgt4_sixVertexFourByFour_noncentralTraceShare_le_four_fifths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourCentralTrace.lean)
-/
@[path]
private lemma fkQgt4_sixVertexFourByFour_noncentralTraceShare_le_four_fifths_eq
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  1 - sixVertexBalancedTraceShare 4 4 (fkQgt4SixVertexWeight q) <= (4 : Real) / 5 := by
-- proof
  apply StatMech.FrontierD.fkQgt4_sixVertexFourByFour_noncentralTraceShare_le_four_fifths hq


-- created on 2026-10-23
