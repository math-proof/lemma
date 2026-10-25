import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronBulk.Part2
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexEvenPositiveHalfProjection_quantile_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronBulk.lean)
-/
@[path]
private lemma sixVertexEvenPositiveHalfProjection_quantile_lower_eq
  {c : Real}
  {k : Nat}
  {p : Fin ((k + 1) + (k + 1)) → Real}
  {j : Fin (k + 1)}
-- given
  (hc : 2 < c)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) p) :
-- imply
  Real.pi * (2 * (j : Real) + 1) < (sixVertexFourWidth 0 k : Real) * sixVertexEvenPositiveHalfProjection (k + 1) p j := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenPositiveHalfProjection_quantile_lower hc hopen hsol j

/--
[sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronBulk.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo_eq
  {c : Real}
  {k : Nat}
  {j : Fin (k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j ∈ Set.Ioo 0 Real.pi := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc k j

/--
[sixVertexCanonicalDensityPerronPositiveHalfRoots_quantile_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronBulk.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronPositiveHalfRoots_quantile_lower_eq
  {c : Real}
  {k : Nat}
  {j : Fin (k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  Real.pi * (2 * (j : Real) + 1) < (sixVertexFourWidth 0 k : Real) * sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronPositiveHalfRoots_quantile_lower hc k j

/--
[sixVertexCanonicalDensityPerronBetheM_norm_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronBulk.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronBetheM_norm_ge_eq
  {c : Real}
  {k : Nat}
  {j : Fin (k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  (c ^ 2 - 2) / 2 ≤ ‖sixVertexBetheM c (sixVertexBethePhase (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronBetheM_norm_ge hc k j

/--
[sixVertexCanonicalDensityPerronBetheM_norm_le_quantile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronBulk.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronBetheM_norm_le_quantile_eq
  {c : Real}
  {k : Nat}
  {j : Fin (k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  ‖sixVertexBetheM c (sixVertexBethePhase (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ ≤ c ^ 2 * (sixVertexFourWidth 0 k : Real) / (2 * (2 * (j : Real) + 1)) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronBetheM_norm_le_quantile hc k j

/--
[sixVertexCanonicalDensityPerronBetheM_log_norm_le_quantile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronBulk.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronBetheM_log_norm_le_quantile_eq
  {c : Real}
  {k : Nat}
  {j : Fin (k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  Real.log ‖sixVertexBetheM c (sixVertexBethePhase (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ ≤ Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / (2 * (2 * (j : Real) + 1))) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronBetheM_log_norm_le_quantile hc k j

/--
[sixVertexCanonicalDensityPerronBetheM_log_norm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronBulk.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronBetheM_log_norm_nonneg_eq
  {c : Real}
  {k : Nat}
  {j : Fin (k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  0 ≤ Real.log ‖sixVertexBetheM c (sixVertexBethePhase (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖ := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronBetheM_log_norm_nonneg hc k j

/--
[sixVertexCanonicalDensityPerronInitialLogContribution_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronBulk.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronInitialLogContribution_nonneg_eq
  {c : Real}
  {J k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  0 ≤ sixVertexCanonicalDensityPerronInitialLogContribution hc J k := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronInitialLogContribution_nonneg hc J k

/--
[sixVertexCanonicalDensityPerronInitialLogContribution_le_factorial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronBulk.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronInitialLogContribution_le_factorial_eq
  {c : Real}
  {J k : Nat}
-- given
  (hc : 2 < c)
  (hJ : J ≤ k + 1) :
-- imply
  sixVertexCanonicalDensityPerronInitialLogContribution hc J k ≤ (2 * ((J : Real) * Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2) - Real.log (J.factorial : Real))) / (sixVertexFourWidth 0 k : Real) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronInitialLogContribution_le_factorial hc hJ

/--
[sixVertexCanonicalDensityPerronInitialLogContribution_le_stirling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronBulk.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronInitialLogContribution_le_stirling_eq
  {c : Real}
  {J k : Nat}
-- given
  (hc : 2 < c)
  (hJ0 : 0 < J)
  (hJ : J ≤ k + 1) :
-- imply
  sixVertexCanonicalDensityPerronInitialLogContribution hc J k ≤ (2 * (J : Real) * (Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / (2 * (J : Real))) + 1)) / (sixVertexFourWidth 0 k : Real) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronInitialLogContribution_le_stirling hc hJ0 hJ

/--
[sixVertexCanonicalDensityPerronInitialLogContribution_tendsto_zero_of_sublinear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronBulk.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronInitialLogContribution_tendsto_zero_of_sublinear_eq
  {c : Real}
  {J : Nat → Nat}
-- given
  (hc : 2 < c)
  (hJ0 : ∀ᶠ k in atTop, 0 < J k)
  (hJle : ∀ᶠ k in atTop, J k ≤ k + 1)
  (hsublinear : Tendsto (fun k : Nat => (J k : Real) / (sixVertexFourWidth 0 k : Real)) atTop (nhds 0)) :
-- imply
  Tendsto (fun k => sixVertexCanonicalDensityPerronInitialLogContribution hc (J k) k) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronInitialLogContribution_tendsto_zero_of_sublinear hc J hJ0 hJle hsublinear

/--
[sixVertexCanonicalDensityPerronInitialLogContribution_log2_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronBulk.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronInitialLogContribution_log2_tendsto_zero_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexCanonicalDensityPerronInitialLogContribution hc (Nat.log2 (k + 1)) k) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronInitialLogContribution_log2_tendsto_zero hc


-- created on 2026-10-23
