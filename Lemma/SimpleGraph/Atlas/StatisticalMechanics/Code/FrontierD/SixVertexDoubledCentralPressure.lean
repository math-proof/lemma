import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDoubledCentralPressure.Part2
open Filter Matrix Topology StatMech StatMech.FrontierD


/--
[sixVertexFullTrace_pow_four_le_boundary_mul_doubledCentralTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDoubledCentralPressure.lean)
-/
@[path]
private lemma sixVertexFullTrace_pow_four_le_boundary_mul_doubledCentralTrace_eq
  {N M : Nat}
  {c : Real}
-- given
  (hN : 0 < N)
  (hM : 0 < M)
  (hNeven : Even N)
  (hMeven : Even M)
  (hc : 0 <= c) :
-- imply
  sixVertexFixedWidthPartitionSum N M c ^ 4 <= (2 : Real) ^ (4 * (N + M)) * Matrix.trace (sixVertexSectorTransfer (N + N) ((N + N) / 2) c ^ (M + M)) := by
-- proof
  apply StatMech.FrontierD.sixVertexFullTrace_pow_four_le_boundary_mul_doubledCentralTrace N M hN hM hNeven hMeven hc

/--
[sixVertexDoubledCentralTrace_le_fullTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDoubledCentralPressure.lean)
-/
@[path]
private lemma sixVertexDoubledCentralTrace_le_fullTrace_eq
  {N M : Nat}
  {c : Real}
-- given
  (hN : 0 < N)
  (hM : 0 < M)
  (hNeven : Even N)
  (hMeven : Even M)
  (hc : 0 <= c) :
-- imply
  Matrix.trace (sixVertexSectorTransfer (N + N) ((N + N) / 2) c ^ (M + M)) <= sixVertexFixedWidthPartitionSum (N + N) (M + M) c := by
-- proof
  apply StatMech.FrontierD.sixVertexDoubledCentralTrace_le_fullTrace N M hN hM hNeven hMeven hc

/--
[four_mul_log_sixVertexFullTrace_le_boundary_add_log_doubledCentral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDoubledCentralPressure.lean)
-/
@[path]
private lemma four_mul_log_sixVertexFullTrace_le_boundary_add_log_doubledCentral_eq
  {N M : Nat}
  {c : Real}
-- given
  (hN : 0 < N)
  (hM : 0 < M)
  (hNeven : Even N)
  (hMeven : Even M)
  (hc : 0 < c) :
-- imply
  4 * Real.log (sixVertexFixedWidthPartitionSum N M c) <= (4 * (N + M) : Nat) * Real.log 2 + Real.log (Matrix.trace (sixVertexSectorTransfer (N + N) ((N + N) / 2) c ^ (M + M))) := by
-- proof
  apply StatMech.FrontierD.four_mul_log_sixVertexFullTrace_le_boundary_add_log_doubledCentral N M hN hM hNeven hMeven hc

/--
[sixVertexLogWidthTop_le_log_two_add_half_doubledCentral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDoubledCentralPressure.lean)
-/
@[path]
private lemma sixVertexLogWidthTop_le_log_two_add_half_doubledCentral_eq
  {N : Nat}
  {c : Real}
-- given
  (hN : 0 < N)
  (hNeven : Even N)
  (hc : 0 < c) :
-- imply
  Real.log (sixVertexWidthTopEigenvalue N c) <= Real.log 2 + Real.log (sixVertexSectorTopEigenvalue (N + N) ((N + N) / 2) (Nat.div_le_self (N + N) 2) c) / 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexLogWidthTop_le_log_two_add_half_doubledCentral N hN hNeven hc

/--
[sixVertexCentralWidthRate_le_fullWidthRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDoubledCentralPressure.lean)
-/
@[path]
private lemma sixVertexCentralWidthRate_le_fullWidthRate_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 0 < c) :
-- imply
  sixVertexCentralWidthRate c k <= sixVertexFullWidthRate c k := by
-- proof
  apply StatMech.FrontierD.sixVertexCentralWidthRate_le_fullWidthRate hc k

/--
[sixVertexFullWidthRate_le_log_two_div_add_doubledCentral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDoubledCentralPressure.lean)
-/
@[path]
private lemma sixVertexFullWidthRate_le_log_two_div_add_doubledCentral_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 0 < c) :
-- imply
  sixVertexFullWidthRate c k <= Real.log 2 / (sixVertexFourWidth 0 k : Real) + sixVertexCentralWidthRate c (2 * k + 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexFullWidthRate_le_log_two_div_add_doubledCentral hc k

/--
[tendsto_sixVertexFullWidthRate_canonicalPerron](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDoubledCentralPressure.lean)
-/
@[path]
private lemma tendsto_sixVertexFullWidthRate_canonicalPerron_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexFullWidthRate c) atTop (nhds (sixVertexAntiferroelectricFreeEnergyValue (sixVertexAntiferroelectricLambda c))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFullWidthRate_canonicalPerron hc

/--
[sixVertexFullAreaDensity_tendsto_widthRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDoubledCentralPressure.lean)
-/
@[path]
private lemma sixVertexFullAreaDensity_tendsto_widthRate_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 0 < c) :
-- imply
  Tendsto (sixVertexFullAreaDensity c k) atTop (nhds (sixVertexFullWidthRate c k)) := by
-- proof
  apply StatMech.FrontierD.sixVertexFullAreaDensity_tendsto_widthRate hc k

/--
[sixVertexFull_iteratedLimit_of_canonicalPerron](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDoubledCentralPressure.lean)
-/
@[path]
private lemma sixVertexFull_iteratedLimit_of_canonicalPerron_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexHasIteratedLimit (sixVertexFullAreaDensity c) (sixVertexAntiferroelectricFreeEnergyValue (sixVertexAntiferroelectricLambda c)) := by
-- proof
  apply StatMech.FrontierD.sixVertexFull_iteratedLimit_of_canonicalPerron hc

/--
[fkQgt4_sixVertexFull_iteratedLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDoubledCentralPressure.lean)
-/
@[path]
private lemma fkQgt4_sixVertexFull_iteratedLimit_eq
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  SixVertexHasIteratedLimit (sixVertexFullAreaDensity (fkQgt4SixVertexWeight q)) (sixVertexAntiferroelectricFreeEnergyValue (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q))) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_sixVertexFull_iteratedLimit hq


-- created on 2026-10-23
