import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootGapFirstOrder
open StatMech StatMech.FrontierD


/--
[abs_width_mul_gap_sub_inv_density_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootGapFirstOrder.lean)
-/
@[path]
private lemma abs_width_mul_gap_sub_inv_density_le_eq
  {N gap finiteDensity density lower mesh densityError cellError : Real}
-- given
  (hN : 0 < N)
  (hgap : 0 <= gap)
  (hlower : 0 < lower)
  (hmeshNonneg : 0 <= mesh)
  (hdensityErrorNonneg : 0 <= densityError)
  (hcellErrorNonneg : 0 <= cellError)
  (hdensity : lower <= density)
  (hmesh : gap <= mesh / N)
  (hdensityError : |finiteDensity - density| <= densityError / N)
  (hcell : |gap * finiteDensity - 1 / N| <= cellError * gap ^ 2) :
-- imply
  |N * gap - 1 / density| <= (cellError * mesh ^ 2 + mesh * densityError) / (lower * N) := by
-- proof
  apply StatMech.FrontierD.abs_width_mul_gap_sub_inv_density_le hN hgap hlower hmeshNonneg hdensityErrorNonneg hcellErrorNonneg hdensity hmesh hdensityError hcell

/--
[abs_width_mul_adjacentBetheGap_sub_inv_density_le_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootGapFirstOrder.lean)
-/
@[path]
private lemma abs_width_mul_adjacentBetheGap_sub_inv_density_le_tail_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) -> Real}
  {j : Fin n}
  {rho : Real -> Real}
  {lower E : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hN : 0 < N)
  (hhalf : 2 * (n + 1) <= N)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hlower : 0 < lower)
  (hrho : lower <= rho (p j.castSucc))
  (hE : 0 <= E)
  (hclose : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c x * (sixVertexFiniteRootDensity c N (n + 1) p x - rho x)| <= E / N) :
-- imply
  |(N : Real) * (p j.succ - p j.castSucc) - 1 / rho (p j.castSucc)| <= ((sixVertexFiniteRootDensityLipschitzConstant c : Real) * (1 / sixVertexTailFiniteDensityFloor c) ^ 2 + (1 / sixVertexTailFiniteDensityFloor c) * (E / ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c))) / (lower * N) := by
-- proof
  apply StatMech.FrontierD.abs_width_mul_adjacentBetheGap_sub_inv_density_le_tail hc htail hN hhalf hopen hsol j hlower hrho hE hclose

/--
[abs_sub_le_of_weighted_abs_sub_le_invWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootGapFirstOrder.lean)
-/
@[path]
private lemma abs_sub_le_of_weighted_abs_sub_le_invWidth_eq
  {N weight wmin E a b : Real}
-- given
  (hN : 0 < N)
  (hwmin : 0 < wmin)
  (hweight : wmin <= weight)
  (h : |weight * (a - b)| <= E / N) :
-- imply
  |a - b| <= (E / wmin) / N := by
-- proof
  apply StatMech.FrontierD.abs_sub_le_of_weighted_abs_sub_le_invWidth hN hwmin hweight h

/--
[sum_sixVertexTheta_zero_of_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootGapFirstOrder.lean)
-/
@[path]
private lemma sum_sixVertexTheta_zero_of_symmetric_eq
  {c : Real}
  {n : Nat}
  {p : Fin n -> Real}
-- given
  (hp : SixVertexRootSymmetric p) :
-- imply
  (∑ k, sixVertexTheta c 0 (p k)) = 0 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexTheta_zero_of_symmetric c hp

/--
[sixVertexBetheCountingFunction_zero_of_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootGapFirstOrder.lean)
-/
@[path]
private lemma sixVertexBetheCountingFunction_zero_of_symmetric_eq
  {c : Real}
  {N : Nat}
  {n : Nat}
  {p : Fin n -> Real}
-- given
  (hp : SixVertexRootSymmetric p) :
-- imply
  sixVertexBetheCountingFunction c N n p 0 = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheCountingFunction_zero_of_symmetric c N hp

/--
[abs_sixVertexBetheCountingFunction_sub_le_of_weightedDensityClose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootGapFirstOrder.lean)
-/
@[path]
private lemma abs_sixVertexBetheCountingFunction_sub_le_of_weightedDensityClose_eq
  {c : Real}
  {N np nq : Nat}
  {p : Fin np -> Real}
  {q : Fin nq -> Real}
  {rho : Real -> Real}
  {EP EQ : Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hpSymm : SixVertexRootSymmetric p)
  (hqSymm : SixVertexRootSymmetric q)
  (hEP : 0 <= EP)
  (hEQ : 0 <= EQ)
  (hpClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c y * (sixVertexFiniteRootDensity c N np p y - rho y)| <= EP / N)
  (hqClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c y * (sixVertexFiniteRootDensity c N nq q y - rho y)| <= EQ / N)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  |sixVertexBetheCountingFunction c N np p x - sixVertexBetheCountingFunction c N nq q x| <= (((EP + EQ) / ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c)) / N) * Real.pi := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexBetheCountingFunction_sub_le_of_weightedDensityClose hc hN hpSymm hqSymm hEP hEQ hpClose hqClose hx

/--
[lower_mul_abs_sub_le_abs_sixVertexBetheCountingFunction_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootGapFirstOrder.lean)
-/
@[path]
private lemma lower_mul_abs_sub_le_abs_sixVertexBetheCountingFunction_sub_eq
  {c : Real}
  {N n : Nat}
  {lower a b : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (p : Fin n -> Real)
  (hlower : 0 <= lower)
  (hdensity : forall x, lower <= sixVertexFiniteRootDensity c N n p x) :
-- imply
  lower * |b - a| <= |sixVertexBetheCountingFunction c N n p b - sixVertexBetheCountingFunction c N n p a| := by
-- proof
  apply StatMech.FrontierD.lower_mul_abs_sub_le_abs_sixVertexBetheCountingFunction_sub hc hN p hlower hdensity

/--
[monotone_sixVertexBetheCountingFunction_of_finiteDensity_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootGapFirstOrder.lean)
-/
@[path]
private lemma monotone_sixVertexBetheCountingFunction_of_finiteDensity_nonneg_eq
  {c : Real}
  {N n : Nat}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (p : Fin n -> Real)
  (hdensity : forall x, 0 <= sixVertexFiniteRootDensity c N n p x) :
-- imply
  Monotone (sixVertexBetheCountingFunction c N n p) := by
-- proof
  apply StatMech.FrontierD.monotone_sixVertexBetheCountingFunction_of_finiteDensity_nonneg hc hN p hdensity

/--
[abs_alignedOffsetIncrement_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootGapFirstOrder.lean)
-/
@[path]
private lemma abs_alignedOffsetIncrement_le_eq
  {N q0 q1 p0 p1 rhoQ rhoP Aq Ap R C : Real}
-- given
  (hN : 0 < N)
  (hR : 0 <= R)
  (hqGap : |N * (q1 - q0) - 1 / rhoQ| <= Aq / N)
  (hpGap : |N * (p1 - p0) - 1 / rhoP| <= Ap / N)
  (hrecip : |1 / rhoQ - 1 / rhoP| <= R * |q0 - p0|)
  (hoffset : |N * (q0 - p0)| <= C) :
-- imply
  |N * (q1 - p1) - N * (q0 - p0)| <= (Aq + Ap + R * C) / N := by
-- proof
  apply StatMech.FrontierD.abs_alignedOffsetIncrement_le hN hR hqGap hpGap hrecip hoffset

/--
[abs_consecutiveGap_mul_finiteRootDensity_sub_inv_width_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootGapFirstOrder.lean)
-/
@[path]
private lemma abs_consecutiveGap_mul_finiteRootDensity_sub_inv_width_le_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n -> Real}
  {i j : Fin n}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hn : n <= N)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N n p)
  (hij : j.val = i.val + 1) :
-- imply
  |(p j - p i) * sixVertexFiniteRootDensity c N n p (p i) - 1 / N| <= (sixVertexFiniteRootDensityLipschitzConstant c : Real) * (p j - p i) ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_consecutiveGap_mul_finiteRootDensity_sub_inv_width_le hc hN hn hopen hsol i j hij

/--
[sixVertexBetheSolution_consecutiveSpacing_upper_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootGapFirstOrder.lean)
-/
@[path]
private lemma sixVertexBetheSolution_consecutiveSpacing_upper_tail_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n -> Real}
  {i j : Fin n}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hN : 0 < N)
  (hhalf : 2 * n <= N)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N n p)
  (hij : j.val = i.val + 1) :
-- imply
  p j - p i <= 1 / ((N : Real) * sixVertexTailFiniteDensityFloor c) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheSolution_consecutiveSpacing_upper_tail hc htail hN hhalf hopen hsol i j hij

/--
[abs_width_mul_consecutiveBetheGap_sub_inv_density_le_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootGapFirstOrder.lean)
-/
@[path]
private lemma abs_width_mul_consecutiveBetheGap_sub_inv_density_le_tail_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n -> Real}
  {i j : Fin n}
  {rho : Real -> Real}
  {lower E : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hN : 0 < N)
  (hhalf : 2 * n <= N)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N n p)
  (hlower : 0 < lower)
  (hrho : lower <= rho (p i))
  (hE : 0 <= E)
  (hclose : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c x * (sixVertexFiniteRootDensity c N n p x - rho x)| <= E / N)
  (hij : j.val = i.val + 1) :
-- imply
  |(N : Real) * (p j - p i) - 1 / rho (p i)| <= ((sixVertexFiniteRootDensityLipschitzConstant c : Real) * (1 / sixVertexTailFiniteDensityFloor c) ^ 2 + (1 / sixVertexTailFiniteDensityFloor c) * (E / ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c))) / (lower * N) := by
-- proof
  apply StatMech.FrontierD.abs_width_mul_consecutiveBetheGap_sub_inv_density_le_tail hc htail hN hhalf hopen hsol i j hlower hrho hE hclose hij

/--
[abs_midpointAlignedOffsetIncrement_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootGapFirstOrder.lean)
-/
@[path]
private lemma abs_midpointAlignedOffsetIncrement_le_eq
  {N q0 q1 p00 p01 p10 p11 rhoQ rhoP0 rhoP1 Aq Ap0 Ap1 D : Real}
-- given
  (hN : 0 < N)
  (hqGap : |N * (q1 - q0) - 1 / rhoQ| <= Aq / N)
  (hp0Gap : |N * (p01 - p00) - 1 / rhoP0| <= Ap0 / N)
  (hp1Gap : |N * (p11 - p10) - 1 / rhoP1| <= Ap1 / N)
  (hmiddle : |1 / rhoQ - (1 / rhoP0 + 1 / rhoP1) / 2| <= D / N) :
-- imply
  |N * (q1 - (p01 + p11) / 2) - N * (q0 - (p00 + p10) / 2)| <= (Aq + (Ap0 + Ap1) / 2 + D) / N := by
-- proof
  apply StatMech.FrontierD.abs_midpointAlignedOffsetIncrement_le hN hqGap hp0Gap hp1Gap hmiddle


-- created on 2026-10-23
