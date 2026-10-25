import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexGapEulerLogs.Part3
open Filter Topology StatMech StatMech.FrontierD


/--
[summable_expEuler](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapEulerLogs.lean)
-/
@[path]
private lemma summable_expEuler_eq
  {t : ℝ}
-- given
  (ht : 0 < t) :
-- imply
  Summable (fun n : ℕ => Real.exp (-2 * Real.pi * t * (n + 1 : ℝ))) := by
-- proof
  apply StatMech.FrontierD.summable_expEuler ht

/--
[summable_sixVertexEulerLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapEulerLogs.lean)
-/
@[path]
private lemma summable_sixVertexEulerLog_eq
  {t : ℝ}
-- given
  (ht : 0 < t) :
-- imply
  Summable (fun n : ℕ => Real.log (1 - Real.exp (-2 * Real.pi * t * (n + 1 : ℝ)))) := by
-- proof
  apply StatMech.FrontierD.summable_sixVertexEulerLog ht

/--
[summable_sixVertexPlusEulerLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapEulerLogs.lean)
-/
@[path]
private lemma summable_sixVertexPlusEulerLog_eq
  {t : ℝ}
-- given
  (ht : 0 < t) :
-- imply
  Summable (fun n : ℕ => Real.log (1 + Real.exp (-2 * Real.pi * t * (n + 1 : ℝ)))) := by
-- proof
  apply StatMech.FrontierD.summable_sixVertexPlusEulerLog ht

/--
[sixVertexPlusEulerLog_eq_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapEulerLogs.lean)
-/
@[path]
private lemma sixVertexPlusEulerLog_eq_sub_eq
  {t : ℝ}
-- given
  (ht : 0 < t) :
-- imply
  sixVertexPlusEulerLog t = sixVertexEulerLog (2 * t) - sixVertexEulerLog t := by
-- proof
  apply StatMech.FrontierD.sixVertexPlusEulerLog_eq_sub ht

/--
[sixVertexAlternatingPlusEulerLog_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapEulerLogs.lean)
-/
@[path]
private lemma sixVertexAlternatingPlusEulerLog_eq_eq
  {t : ℝ}
-- given
  (ht : 0 < t) :
-- imply
  sixVertexAlternatingPlusEulerLog t = sixVertexPlusEulerLog t - 2 * sixVertexPlusEulerLog (2 * t) := by
-- proof
  apply StatMech.FrontierD.sixVertexAlternatingPlusEulerLog_eq ht

/--
[sixVertexAlternatingPlusEulerLog_eq_euler](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapEulerLogs.lean)
-/
@[path]
private lemma sixVertexAlternatingPlusEulerLog_eq_euler_eq
  {t : ℝ}
-- given
  (ht : 0 < t) :
-- imply
  sixVertexAlternatingPlusEulerLog t = 3 * sixVertexEulerLog (2 * t) - sixVertexEulerLog t - 2 * sixVertexEulerLog (4 * t) := by
-- proof
  apply StatMech.FrontierD.sixVertexAlternatingPlusEulerLog_eq_euler ht

/--
[sixVertexGapAlternatingLogSeries_eq_euler](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapEulerLogs.lean)
-/
@[path]
private lemma sixVertexGapAlternatingLogSeries_eq_euler_eq
  {lam : ℝ}
-- given
  (hlam : 0 < lam) :
-- imply
  sixVertexGapAlternatingLogSeries lam = 3 * sixVertexEulerLog (2 * (lam / Real.pi)) - sixVertexEulerLog (lam / Real.pi) - 2 * sixVertexEulerLog (4 * (lam / Real.pi)) := by
-- proof
  apply StatMech.FrontierD.sixVertexGapAlternatingLogSeries_eq_euler hlam

/--
[sixVertexOddEulerRatioLog_eq_euler](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapEulerLogs.lean)
-/
@[path]
private lemma sixVertexOddEulerRatioLog_eq_euler_eq
  {t : ℝ}
-- given
  (ht : 0 < t) :
-- imply
  sixVertexOddEulerRatioLog t = 3 * sixVertexEulerLog (2 * t) - 2 * sixVertexEulerLog t - sixVertexEulerLog (4 * t) := by
-- proof
  apply StatMech.FrontierD.sixVertexOddEulerRatioLog_eq_euler ht

/--
[sixVertexDualGapPowerSeries_exp_eq_oddEuler](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapEulerLogs.lean)
-/
@[path]
private lemma sixVertexDualGapPowerSeries_exp_eq_oddEuler_eq
  {t : ℝ} :
-- imply
  sixVertexDualGapPowerSeries (Real.exp (-2 * Real.pi * t)) = 4 * sixVertexOddEulerRatioLog t := by
-- proof
  apply StatMech.FrontierD.sixVertexDualGapPowerSeries_exp_eq_oddEuler t


-- created on 2026-10-23
