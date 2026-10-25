import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallis.Part4
open StatMech StatMech.FrontierD


/--
[abs_log_sub_log_le_of_pos_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma abs_log_sub_log_le_of_pos_lower_eq
  {lower x y : Real}
-- given
  (hlower : 0 < lower)
  (hlowerX : lower <= x)
  (hlowerY : lower <= y) :
-- imply
  |Real.log x - Real.log y| <= |x - y| / lower := by
-- proof
  apply StatMech.FrontierD.abs_log_sub_log_le_of_pos_lower hlower hlowerX hlowerY

/--
[sixVertexBetheDesingularizedLogObservable_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma sixVertexBetheDesingularizedLogObservable_eq_eq
  {c x : Real}
-- given
  (hc : 2 < c)
  (hx : x ∈ Set.Ioo 0 Real.pi) :
-- imply
  sixVertexBetheDesingularizedLogObservable c x = sixVertexBetheLogObservable c x + Real.log x := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheDesingularizedLogObservable_eq hc hx

/--
[sixVertexBetheDesingularizedLogObservable_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma sixVertexBetheDesingularizedLogObservable_zero_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexBetheDesingularizedLogObservable c 0 = Real.log (c ^ 2) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheDesingularizedLogObservable_zero hc

/--
[sixVertexBetheDesingularizedLogObservable_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma sixVertexBetheDesingularizedLogObservable_pi_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexBetheDesingularizedLogObservable c Real.pi = Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) + Real.log Real.pi := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheDesingularizedLogObservable_pi hc

/--
[continuousOn_sixVertexBetheDesingularizedLogObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma continuousOn_sixVertexBetheDesingularizedLogObservable_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  ContinuousOn (sixVertexBetheDesingularizedLogObservable c) (Set.Icc 0 Real.pi) := by
-- proof
  apply StatMech.FrontierD.continuousOn_sixVertexBetheDesingularizedLogObservable hc

/--
[abs_sinc_sub_one_le_sq_div_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma abs_sinc_sub_one_le_sq_div_four_eq
  {x : Real}
-- given
  (hx : |x| <= 1) :
-- imply
  |Real.sinc x - 1| <= x ^ 2 / 4 := by
-- proof
  apply StatMech.FrontierD.abs_sinc_sub_one_le_sq_div_four hx

/--
[hasDerivAt_sinc_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma hasDerivAt_sinc_zero_eq :
-- imply
  HasDerivAt Real.sinc 0 0 := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sinc_zero

/--
[hasDerivAt_sinc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma hasDerivAt_sinc_eq
  {x : Real} :
-- imply
  HasDerivAt Real.sinc (sixVertexSincDerivative x) x := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sinc x

/--
[sixVertexOddWallisHalfProduct_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma sixVertexOddWallisHalfProduct_sq_eq
  {m : Nat} :
-- imply
  sixVertexOddWallisHalfProduct m ^ 2 = 1 / (((2 * m + 1 : Nat) : Real) * Real.Wallis.W m) := by
-- proof
  apply StatMech.FrontierD.sixVertexOddWallisHalfProduct_sq m

/--
[tendsto_sixVertexOddWallisReferenceProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma tendsto_sixVertexOddWallisReferenceProduct_eq
  {s : Nat} :
-- imply
  Tendsto (fun k => (sixVertexFourWidth (2 * s + 1) k : Real) * sixVertexOddWallisHalfProduct (s + k + 1) ^ 2) atTop (nhds (4 / Real.pi)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexOddWallisReferenceProduct s

/--
[sixVertexCanonicalOddZeroPrefactor_eq_finiteDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma sixVertexCanonicalOddZeroPrefactor_eq_finiteDensity_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexCanonicalFixedOddDensityWitness hc s k (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)) :
-- imply
  sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth (2 * s + 1) k) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k) (sixVertexOddCentralIndex (s + k + 1)) = c ^ 2 * (sixVertexFourWidth (2 * s + 1) k : Real) * (2 * Real.pi) * sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (((s + k + 1) + 1) + (s + k + 1)) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k) 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddZeroPrefactor_eq_finiteDensity hc s k hfixed

/--
[tendsto_sixVertexCanonicalOddFiniteDensity_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddFiniteDensity_zero_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (((s + k + 1) + 1) + (s + k + 1)) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k) 0) atTop (nhds (sixVertexFourierPhysicalDensity c hc 0)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddFiniteDensity_zero hc s

/--
[sixVertexCanonicalOddLeftHalfRoot_countingFunction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma sixVertexCanonicalOddLeftHalfRoot_countingFunction_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (s + k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexBetheCountingFunction c (sixVertexFourWidth (2 * s + 1) k) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) (sixVertexCanonicalOddLeftHalfRoot hc s k j) = ((j : Real) + 1 / 2) / sixVertexFourWidth (2 * s + 1) k := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddLeftHalfRoot_countingFunction hc s k j

/--
[sixVertexCanonicalOddRightHalfRoot_countingFunction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma sixVertexCanonicalOddRightHalfRoot_countingFunction_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (s + k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexBetheCountingFunction c (sixVertexFourWidth (2 * s + 1) k) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) (sixVertexCanonicalOddRightHalfRoot hc s k j) = ((j : Real) + 3 / 2) / sixVertexFourWidth (2 * s + 1) k := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddRightHalfRoot_countingFunction hc s k j

/--
[abs_sixVertexCanonicalOddMidpointHalfRoot_countingFunction_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma abs_sixVertexCanonicalOddMidpointHalfRoot_countingFunction_sub_le_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (s + k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  let N := sixVertexFourWidth (2 * s + 1) k let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1) let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) |sixVertexBetheCountingFunction c N n p (sixVertexCanonicalOddMidpointHalfRoot hc s k j) - ((j : Real) + 1) / N| <= (sixVertexFiniteRootDensityLipschitzConstant c : Real) * (sixVertexCanonicalOddRightHalfRoot hc s k j - sixVertexCanonicalOddLeftHalfRoot hc s k j) ^ 2 / 4 := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexCanonicalOddMidpointHalfRoot_countingFunction_sub_le hc s k j

/--
[sixVertexCanonicalOddHalfRoot_gap_le_of_densityLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma sixVertexCanonicalOddHalfRoot_gap_le_of_densityLower_eq
  {c : Real}
  {s k : Nat}
  {lower : Real}
  {j : Fin (s + k + 1)}
-- given
  (hc : 2 < c)
  (hlower : 0 < lower)
  (hdensity : forall x, lower <= sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x) :
-- imply
  sixVertexCanonicalOddRightHalfRoot hc s k j - sixVertexCanonicalOddLeftHalfRoot hc s k j <= 1 / ((sixVertexFourWidth (2 * s + 1) k : Real) * lower) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddHalfRoot_gap_le_of_densityLower hc s k hlower hdensity j

/--
[abs_sixVertexCanonicalOddMidpointHalfRoot_countingFunction_sub_le_invWidthSq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma abs_sixVertexCanonicalOddMidpointHalfRoot_countingFunction_sub_le_invWidthSq_eq
  {c : Real}
  {s k : Nat}
  {lower : Real}
  {j : Fin (s + k + 1)}
-- given
  (hc : 2 < c)
  (hlower : 0 < lower)
  (hdensity : forall x, lower <= sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x) :
-- imply
  let N := sixVertexFourWidth (2 * s + 1) k let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1) let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) |sixVertexBetheCountingFunction c N n p (sixVertexCanonicalOddMidpointHalfRoot hc s k j) - ((j : Real) + 1) / N| <= (sixVertexFiniteRootDensityLipschitzConstant c : Real) / (4 * ((N : Real) * lower) ^ 2) := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexCanonicalOddMidpointHalfRoot_countingFunction_sub_le_invWidthSq hc s k hlower hdensity j

/--
[abs_log_sixVertexCanonicalOddMidpointCounting_sub_reference_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma abs_log_sixVertexCanonicalOddMidpointCounting_sub_reference_le_eq
  {c : Real}
  {s k : Nat}
  {lower : Real}
  {j : Fin (s + k + 1)}
-- given
  (hc : 2 < c)
  (hlower : 0 < lower)
  (hdensity : forall x, lower <= sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x) :
-- imply
  let N := sixVertexFourWidth (2 * s + 1) k let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1) let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) |Real.log (sixVertexBetheCountingFunction c N n p (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) - Real.log (((j : Real) + 1) / N)| <= (sixVertexFiniteRootDensityLipschitzConstant c : Real) / (2 * (N : Real) * lower ^ 2 * ((j : Real) + 1)) := by
-- proof
  apply StatMech.FrontierD.abs_log_sixVertexCanonicalOddMidpointCounting_sub_reference_le hc s k hlower hdensity j

/--
[abs_sum_log_sixVertexCanonicalOddMidpointCounting_sub_reference_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma abs_sum_log_sixVertexCanonicalOddMidpointCounting_sub_reference_le_eq
  {c : Real}
  {s k : Nat}
  {lower : Real}
-- given
  (hc : 2 < c)
  (hlower : 0 < lower)
  (hdensity : forall x, lower <= sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x) :
-- imply
  let N := sixVertexFourWidth (2 * s + 1) k let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1) let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) |∑ j : Fin (s + k + 1), (Real.log (sixVertexBetheCountingFunction c N n p (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) - Real.log (((j : Real) + 1) / N))| <= ((sixVertexFiniteRootDensityLipschitzConstant c : Real) / (2 * (N : Real) * lower ^ 2)) * (1 + Real.log (s + k + 1 : Nat)) := by
-- proof
  apply StatMech.FrontierD.abs_sum_log_sixVertexCanonicalOddMidpointCounting_sub_reference_le hc s k hlower hdensity

/--
[tendsto_sum_log_sixVertexCanonicalOddMidpointCounting_sub_reference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma tendsto_sum_log_sixVertexCanonicalOddMidpointCounting_sub_reference_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => let N := sixVertexFourWidth (2 * s + 1) k let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1) let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) ∑ j : Fin (s + k + 1), (Real.log (sixVertexBetheCountingFunction c N n p (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) - Real.log (((j : Real) + 1) / N))) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sum_log_sixVertexCanonicalOddMidpointCounting_sub_reference hc s

/--
[sixVertexOddWallisReferenceLogSum_eq_log](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma sixVertexOddWallisReferenceLogSum_eq_log_eq
  {m : Nat} :
-- imply
  sixVertexOddWallisReferenceLogSum m = Real.log (sixVertexOddWallisHalfProduct m) := by
-- proof
  apply StatMech.FrontierD.sixVertexOddWallisReferenceLogSum_eq_log m

/--
[tendsto_sixVertexOddWallisReferenceLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma tendsto_sixVertexOddWallisReferenceLog_eq
  {s : Nat} :
-- imply
  Tendsto (fun k => Real.log (sixVertexFourWidth (2 * s + 1) k : Real) + 2 * sixVertexOddWallisReferenceLogSum (s + k + 1)) atTop (nhds (Real.log (4 / Real.pi))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexOddWallisReferenceLog s

/--
[tendsto_sixVertexCanonicalOddCountingWallisLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddCountingWallisLog_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => let N := sixVertexFourWidth (2 * s + 1) k let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1) let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) Real.log (N : Real) + 2 * ∑ j : Fin (s + k + 1), (Real.log (sixVertexBetheCountingFunction c N n p (sixVertexCanonicalOddLeftHalfRoot hc s k j)) - Real.log (sixVertexBetheCountingFunction c N n p (sixVertexCanonicalOddMidpointHalfRoot hc s k j)))) atTop (nhds (Real.log (4 / Real.pi))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddCountingWallisLog hc s


-- created on 2026-10-23
