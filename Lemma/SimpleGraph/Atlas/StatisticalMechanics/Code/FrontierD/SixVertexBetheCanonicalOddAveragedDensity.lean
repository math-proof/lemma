import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddAveragedDensity
open StatMech StatMech.FrontierD


/--
[lipschitzOnWith_primitive_div_id_Ioi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensity.lean)
-/
@[path]
private lemma lipschitzOnWith_primitive_div_id_Ioi_eq
  {F rho : Real -> Real}
  {C : NNReal}
-- given
  (hF : forall x, HasDerivAt F (rho x) x)
  (hF0 : F 0 = 0)
  (hrho : LipschitzWith C rho) :
-- imply
  LipschitzOnWith C (fun x => F x / x) (Set.Ioi 0) := by
-- proof
  apply StatMech.FrontierD.lipschitzOnWith_primitive_div_id_Ioi hF hF0 hrho

/--
[primitive_div_id_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensity.lean)
-/
@[path]
private lemma primitive_div_id_lower_eq
  {F rho : Real -> Real}
  {lower x : Real}
-- given
  (hF : forall y, HasDerivAt F (rho y) y)
  (hF0 : F 0 = 0)
  (hcont : Continuous rho)
  (hx : 0 < x)
  (hrho : forall y : Set.Icc (0 : Real) x, lower <= rho y) :
-- imply
  lower <= F x / x := by
-- proof
  apply StatMech.FrontierD.primitive_div_id_lower hF hF0 hcont hx hrho

/--
[abs_primitive_midpoint_defect_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensity.lean)
-/
@[path]
private lemma abs_primitive_midpoint_defect_le_eq
  {F rho : Real -> Real}
  {C : NNReal}
  {a b : Real}
-- given
  (hF : forall x, HasDerivAt F (rho x) x)
  (hrho : LipschitzWith C rho) :
-- imply
  |F ((a + b) / 2) - (F a + F b) / 2| <= (C : Real) * (b - a) ^ 2 / 4 := by
-- proof
  apply StatMech.FrontierD.abs_primitive_midpoint_defect_le hF hrho a b

/--
[abs_primitive_div_id_midpoint_defect_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensity.lean)
-/
@[path]
private lemma abs_primitive_div_id_midpoint_defect_le_eq
  {F rho : Real -> Real}
  {C : NNReal}
  {a b : Real}
-- given
  (hF : forall x, HasDerivAt F (rho x) x)
  (hF0 : F 0 = 0)
  (hrho : LipschitzWith C rho)
  (ha : 0 < a)
  (hab : a <= b) :
-- imply
  let m := (a + b) / 2 |F m / m - (F a / a + F b / b) / 2| <= (C : Real) * (b - a) ^ 2 / (2 * m) := by
-- proof
  apply StatMech.FrontierD.abs_primitive_div_id_midpoint_defect_le hF hF0 hrho ha hab

/--
[abs_primitive_div_id_sub_deriv_zero_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensity.lean)
-/
@[path]
private lemma abs_primitive_div_id_sub_deriv_zero_le_eq
  {F rho : Real -> Real}
  {C : NNReal}
  {x : Real}
-- given
  (hF : forall x, HasDerivAt F (rho x) x)
  (hF0 : F 0 = 0)
  (hrho : LipschitzWith C rho)
  (hx : 0 < x) :
-- imply
  |F x / x - rho 0| <= (C : Real) * x := by
-- proof
  apply StatMech.FrontierD.abs_primitive_div_id_sub_deriv_zero_le hF hF0 hrho hx

/--
[abs_two_log_average_sub_log_sub_log_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensity.lean)
-/
@[path]
private lemma abs_two_log_average_sub_log_sub_log_le_eq
  {lower x y : Real}
-- given
  (hlower : 0 < lower)
  (hx : lower <= x)
  (hy : lower <= y) :
-- imply
  |2 * Real.log ((x + y) / 2) - Real.log x - Real.log y| <= (x - y) ^ 2 / (4 * lower ^ 2) := by
-- proof
  apply StatMech.FrontierD.abs_two_log_average_sub_log_sub_log_le hlower hx hy

/--
[abs_two_log_sub_two_log_le_of_pos_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensity.lean)
-/
@[path]
private lemma abs_two_log_sub_two_log_le_of_pos_lower_eq
  {lower x y : Real}
-- given
  (hlower : 0 < lower)
  (hx : lower <= x)
  (hy : lower <= y) :
-- imply
  |2 * Real.log x - 2 * Real.log y| <= 2 * |x - y| / lower := by
-- proof
  apply StatMech.FrontierD.abs_two_log_sub_two_log_le_of_pos_lower hlower hx hy

/--
[abs_two_log_primitive_div_id_midpoint_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensity.lean)
-/
@[path]
private lemma abs_two_log_primitive_div_id_midpoint_sub_le_eq
  {F rho : Real -> Real}
  {C : NNReal}
  {lower a b : Real}
-- given
  (hF : forall x, HasDerivAt F (rho x) x)
  (hF0 : F 0 = 0)
  (hrho : LipschitzWith C rho)
  (hlower : 0 < lower)
  (ha : 0 < a)
  (hab : a <= b)
  (hlowerA : forall x : Set.Icc a b, lower <= F x / x) :
-- imply
  let m := (a + b) / 2 |2 * Real.log (F m / m) - Real.log (F a / a) - Real.log (F b / b)| <= (C : Real) * (b - a) ^ 2 / (m * lower) + (C : Real) ^ 2 * (b - a) ^ 2 / (4 * lower ^ 2) := by
-- proof
  apply StatMech.FrontierD.abs_two_log_primitive_div_id_midpoint_sub_le hF hF0 hrho hlower ha hab hlowerA

/--
[lipschitzOnWith_sixVertexCanonicalOddCounting_div_id](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensity.lean)
-/
@[path]
private lemma lipschitzOnWith_sixVertexCanonicalOddCounting_div_id_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  let N := sixVertexFourWidth (2 * s + 1) k let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1) let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) LipschitzOnWith (sixVertexFiniteRootDensityLipschitzConstant c) (fun x => sixVertexBetheCountingFunction c N n p x / x) (Set.Ioi 0) := by
-- proof
  apply StatMech.FrontierD.lipschitzOnWith_sixVertexCanonicalOddCounting_div_id hc s k

/--
[abs_sixVertexCanonicalOddAveragedDensity_midpointSecondDifference_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensity.lean)
-/
@[path]
private lemma abs_sixVertexCanonicalOddAveragedDensity_midpointSecondDifference_le_eq
  {c : Real}
  {s k : Nat}
  {lower : Real}
  {j : Fin (s + k + 1)}
-- given
  (hc : 2 < c)
  (hlower : 0 < lower)
  (hdensity : forall x, lower <= sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x) :
-- imply
  let N := sixVertexFourWidth (2 * s + 1) k let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1) let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) let F := sixVertexBetheCountingFunction c N n p let a := sixVertexCanonicalOddLeftHalfRoot hc s k j let b := sixVertexCanonicalOddRightHalfRoot hc s k j let m := sixVertexCanonicalOddMidpointHalfRoot hc s k j |2 * Real.log (F m / m) - Real.log (F a / a) - Real.log (F b / b)| <= (sixVertexFiniteRootDensityLipschitzConstant c : Real) * (b - a) ^ 2 / (m * lower) + (sixVertexFiniteRootDensityLipschitzConstant c : Real) ^ 2 * (b - a) ^ 2 / (4 * lower ^ 2) := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexCanonicalOddAveragedDensity_midpointSecondDifference_le hc s k hlower hdensity j

/--
[abs_sixVertexCanonicalOddAveragedDensity_midpointSecondDifference_le_invWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensity.lean)
-/
@[path]
private lemma abs_sixVertexCanonicalOddAveragedDensity_midpointSecondDifference_le_invWidth_eq
  {c : Real}
  {s k : Nat}
  {lower : Real}
  {j : Fin (s + k + 1)}
-- given
  (hc : 2 < c)
  (hlower : 0 < lower)
  (hdensity : forall x, lower <= sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x) :
-- imply
  let N := sixVertexFourWidth (2 * s + 1) k let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1) let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) let F := sixVertexBetheCountingFunction c N n p let a := sixVertexCanonicalOddLeftHalfRoot hc s k j let b := sixVertexCanonicalOddRightHalfRoot hc s k j let m := sixVertexCanonicalOddMidpointHalfRoot hc s k j |2 * Real.log (F m / m) - Real.log (F a / a) - Real.log (F b / b)| <= (sixVertexFiniteRootDensityLipschitzConstant c : Real) / ((N : Real) * lower ^ 3 * Real.pi * (2 * (j : Real) + 1)) + (sixVertexFiniteRootDensityLipschitzConstant c : Real) ^ 2 / (4 * (N : Real) ^ 2 * lower ^ 4) := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexCanonicalOddAveragedDensity_midpointSecondDifference_le_invWidth hc s k hlower hdensity j

/--
[abs_sum_sixVertexCanonicalOddAveragedDensity_midpointSecondDifference_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensity.lean)
-/
@[path]
private lemma abs_sum_sixVertexCanonicalOddAveragedDensity_midpointSecondDifference_le_eq
  {c : Real}
  {s k : Nat}
  {lower : Real}
-- given
  (hc : 2 < c)
  (hlower : 0 < lower)
  (hdensity : forall x, lower <= sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x) :
-- imply
  let N := sixVertexFourWidth (2 * s + 1) k let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1) let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) let F := sixVertexBetheCountingFunction c N n p |∑ j : Fin (s + k + 1), (2 * Real.log (F (sixVertexCanonicalOddMidpointHalfRoot hc s k j) / sixVertexCanonicalOddMidpointHalfRoot hc s k j) - Real.log (F (sixVertexCanonicalOddLeftHalfRoot hc s k j) / sixVertexCanonicalOddLeftHalfRoot hc s k j) - Real.log (F (sixVertexCanonicalOddRightHalfRoot hc s k j) / sixVertexCanonicalOddRightHalfRoot hc s k j))| <= ((sixVertexFiniteRootDensityLipschitzConstant c : Real) / ((N : Real) * lower ^ 3 * Real.pi)) * (1 + Real.log (s + k + 1 : Nat)) + (s + k + 1 : Real) * ((sixVertexFiniteRootDensityLipschitzConstant c : Real) ^ 2 / (4 * (N : Real) ^ 2 * lower ^ 4)) := by
-- proof
  apply StatMech.FrontierD.abs_sum_sixVertexCanonicalOddAveragedDensity_midpointSecondDifference_le hc s k hlower hdensity

/--
[tendsto_sum_sixVertexCanonicalOddAveragedDensity_midpointSecondDifference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensity.lean)
-/
@[path]
private lemma tendsto_sum_sixVertexCanonicalOddAveragedDensity_midpointSecondDifference_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => let N := sixVertexFourWidth (2 * s + 1) k let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1) let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) let F := sixVertexBetheCountingFunction c N n p ∑ j : Fin (s + k + 1), (2 * Real.log (F (sixVertexCanonicalOddMidpointHalfRoot hc s k j) / sixVertexCanonicalOddMidpointHalfRoot hc s k j) - Real.log (F (sixVertexCanonicalOddLeftHalfRoot hc s k j) / sixVertexCanonicalOddLeftHalfRoot hc s k j) - Real.log (F (sixVertexCanonicalOddRightHalfRoot hc s k j) / sixVertexCanonicalOddRightHalfRoot hc s k j))) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sum_sixVertexCanonicalOddAveragedDensity_midpointSecondDifference hc s

/--
[tendsto_sixVertexCanonicalOddHalfFilledFiniteDensity_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensity.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddHalfFilledFiniteDensity_zero_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) 0) atTop (nhds (sixVertexFourierPhysicalDensity c hc 0)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddHalfFilledFiniteDensity_zero hc s

/--
[two_sum_sixVertexCanonicalOddMidpoint_sub_eq_boundary_add_secondDifference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddAveragedDensity.lean)
-/
@[path]
private lemma two_sum_sixVertexCanonicalOddMidpoint_sub_eq_boundary_add_secondDifference_eq
  {c : Real}
  {s k : Nat}
-- given
  (f : Real -> Real)
  (hc : 2 < c) :
-- imply
  2 * ∑ j : Fin (s + k + 1), (f (sixVertexCanonicalOddMidpointHalfRoot hc s k j) - f (sixVertexCanonicalOddLeftHalfRoot hc s k j)) = f (sixVertexCanonicalOddBoundaryHalfRoot hc s k ⟨0, Nat.succ_pos s⟩) - f (sixVertexCanonicalOddLeftHalfRoot hc s k ⟨0, by omega⟩) + ∑ j : Fin (s + k + 1), (2 * f (sixVertexCanonicalOddMidpointHalfRoot hc s k j) - f (sixVertexCanonicalOddLeftHalfRoot hc s k j) - f (sixVertexCanonicalOddRightHalfRoot hc s k j)) := by
-- proof
  apply StatMech.FrontierD.two_sum_sixVertexCanonicalOddMidpoint_sub_eq_boundary_add_secondDifference f hc s k


-- created on 2026-10-23
