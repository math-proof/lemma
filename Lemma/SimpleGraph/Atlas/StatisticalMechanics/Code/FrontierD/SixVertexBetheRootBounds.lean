import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootBounds.Part2
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexSelectedBetheM_norm_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootBounds.lean)
-/
@[path]
private lemma sixVertexSelectedBetheM_norm_ge_eq
  {c : Real}
  {k : Nat}
  {j : Fin (k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  (c ^ 2 - 2) / 2 ≤ ‖sixVertexBetheM c (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedBetheM_norm_ge hc k j

/--
[sixVertexSelectedBetheM_log_norm_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootBounds.lean)
-/
@[path]
private lemma sixVertexSelectedBetheM_log_norm_ge_eq
  {c : Real}
  {k : Nat}
  {j : Fin (k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  Real.log ((c ^ 2 - 2) / 2) ≤ Real.log ‖sixVertexBetheM c (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedBetheM_log_norm_ge hc k j

/--
[sixVertexSelectedRootAverage_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootBounds.lean)
-/
@[path]
private lemma sixVertexSelectedRootAverage_ge_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Real.log ((c ^ 2 - 2) / 2) / 2 ≤ sixVertexSymmetricBetheRootAverage c (sixVertexPositiveHalfBetheRootFamily hc) k := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedRootAverage_ge hc k

/--
[sixVertexHalfFilledBetheCandidateRate_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootBounds.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheCandidateRate_ge_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Real.log ((c ^ 2 - 2) / 2) / 2 ≤ sixVertexHalfFilledBetheCandidateRate hc k := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheCandidateRate_ge hc k

/--
[sixVertexSelectedBetheM_norm_le_quantile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootBounds.lean)
-/
@[path]
private lemma sixVertexSelectedBetheM_norm_le_quantile_eq
  {c : Real}
  {k : Nat}
  {j : Fin (k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  ‖sixVertexBetheM c (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ ≤ c ^ 2 * (sixVertexFourWidth 0 k : Real) / (2 * (2 * (j : Real) + 1)) := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedBetheM_norm_le_quantile hc k j

/--
[sixVertexSelectedBetheM_log_norm_le_quantile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootBounds.lean)
-/
@[path]
private lemma sixVertexSelectedBetheM_log_norm_le_quantile_eq
  {c : Real}
  {k : Nat}
  {j : Fin (k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  Real.log ‖sixVertexBetheM c (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖ ≤ Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / (2 * (2 * (j : Real) + 1))) := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedBetheM_log_norm_le_quantile hc k j

/--
[sixVertexSelectedInitialLogContribution_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootBounds.lean)
-/
@[path]
private lemma sixVertexSelectedInitialLogContribution_bounds_eq
  {c : Real}
  {J k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  0 ≤ sixVertexSelectedInitialLogContribution hc J k ∧ sixVertexSelectedInitialLogContribution hc J k ≤ (2 * (J : Real) * Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2)) / (sixVertexFourWidth 0 k : Real) := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedInitialLogContribution_bounds hc J k

/--
[sixVertexSelectedInitialLogContribution_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootBounds.lean)
-/
@[path]
private lemma sixVertexSelectedInitialLogContribution_tendsto_zero_eq
  {c : Real}
  {J : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexSelectedInitialLogContribution hc J) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedInitialLogContribution_tendsto_zero hc J

/--
[sixVertexSelectedInitialLogContribution_tendsto_zero_of_schedule](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootBounds.lean)
-/
@[path]
private lemma sixVertexSelectedInitialLogContribution_tendsto_zero_of_schedule_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (J : Nat -> Nat)
  (hscale : Tendsto (fun k : Nat => (2 * (J k : Real) * Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2)) / (sixVertexFourWidth 0 k : Real)) atTop (nhds 0)) :
-- imply
  Tendsto (fun k => sixVertexSelectedInitialLogContribution hc (J k) k) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedInitialLogContribution_tendsto_zero_of_schedule hc J hscale

/--
[sixVertexSelectedInitialLogContribution_log2_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootBounds.lean)
-/
@[path]
private lemma sixVertexSelectedInitialLogContribution_log2_tendsto_zero_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexSelectedInitialLogContribution hc (Nat.log2 (k + 1)) k) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedInitialLogContribution_log2_tendsto_zero hc

/--
[sixVertex_log2Cutoff_tendsto_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootBounds.lean)
-/
@[path]
private lemma sixVertex_log2Cutoff_tendsto_atTop_eq :
-- imply
  Tendsto (fun k : Nat => Nat.log2 (k + 1)) atTop atTop := by
-- proof
  apply StatMech.FrontierD.sixVertex_log2Cutoff_tendsto_atTop

/--
[sixVertex_log2Cutoff_div_width_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootBounds.lean)
-/
@[path]
private lemma sixVertex_log2Cutoff_div_width_tendsto_zero_eq :
-- imply
  Tendsto (fun k : Nat => (Nat.log2 (k + 1) : Real) / (k + 1 : Real)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.sixVertex_log2Cutoff_div_width_tendsto_zero


-- created on 2026-10-23
