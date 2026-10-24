import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.TriangularSharpnessCritical
open Finset Set Filter Topology MeasureTheory SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triangularBoxToBuffered_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBoxToBuffered_injective_eq
  {k : Nat} :
-- imply
  Function.Injective (triangularBoxToBuffered k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBoxToBuffered_injective k

/--
[triangularBoxToBuffered_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBoxToBuffered_adjMatch_eq
  {k : Nat} :
-- imply
  ocd_AdjMatch (triangularBoxGraph (2 * k)) (triangular.bufferedGraph (2 * k)) (triangularBoxToBuffered k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBoxToBuffered_adjMatch k

/--
[triangularCenteredShellFullEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularCenteredShellFullEvent_increasing_eq
  {R k : Nat} :
-- imply
  IsIncreasing (triangularCenteredShellFullEvent R k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularCenteredShellFullEvent_increasing R k

/--
[triangularBufferedInnerShellEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBufferedInnerShellEvent_increasing_eq
  {k : Nat} :
-- imply
  IsIncreasing (triangularBufferedInnerShellEvent k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBufferedInnerShellEvent_increasing k

/--
[triangularBoxToBufferedAt_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBoxToBufferedAt_injective_eq
  {k m : Nat}
-- given
  (hkm : 2 * k ≤ triangular.bufferedRadius m) :
-- imply
  Function.Injective (triangularBoxToBufferedAt k m hkm) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBoxToBufferedAt_injective k m hkm

/--
[triangularBoxToBufferedAt_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBoxToBufferedAt_adjMatch_eq
  {k m : Nat}
-- given
  (hkm : 2 * k ≤ triangular.bufferedRadius m) :
-- imply
  ocd_AdjMatch (triangularBoxGraph (2 * k)) (triangular.bufferedGraph m) (triangularBoxToBufferedAt k m hkm) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBoxToBufferedAt_adjMatch k m hkm

/--
[triangularBoxToBufferedAt_not_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBoxToBufferedAt_not_boundary_eq
  {k m : Nat}
  {x : TriangularBoxVertex (2 * k)}
-- given
  (hkm : 2 * k < m) :
-- imply
  ¬ triangular.bufferedBoundary m (triangularBoxToBufferedAt k m ((triangular.id_le_bufferedRadius (2 * k)).trans (triangular.bufferedRadius_strictMono.monotone hkm.le)) x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBoxToBufferedAt_not_boundary k m hkm x

/--
[triangularBoxToBufferedAt_boundary_of_adj_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBoxToBufferedAt_boundary_of_adj_outside_eq
  {k : Nat}
  {x : TriangularBoxVertex (2 * k)}
  {z : Site 2}
-- given
  (hk : 1 ≤ k)
  (hxz : triangularGraph.Adj x.1 z)
  (hz : z ∉ box 2 (2 * k)) :
-- imply
  x ∈ triangularBoxShell (2 * k) (2 * k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBoxToBufferedAt_boundary_of_adj_outside k hk x z hxz hz

/--
[triangularBoxToBufferedAt_inducedWiring_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBoxToBufferedAt_inducedWiring_le_eq
  {k m : Nat}
  {psi : ConfigSpace (Sym2 (triangular.BufferedVertex m))}
-- given
  (hk : 1 ≤ k)
  (hkm : 2 * k < m) :
-- imply
  ocd_inducedWiring (triangular.bufferedGraph m) (triangularBoxToBufferedAt k m ((triangular.id_le_bufferedRadius (2 * k)).trans (triangular.bufferedRadius_strictMono.monotone hkm.le))) (triangular.bufferedBoundary m) psi ≤ boundaryCliqueGraph (fun x => x ∈ triangularBoxShell (2 * k) (2 * k)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBoxToBufferedAt_inducedWiring_le k m hk hkm psi

/--
[triangularBufferedInnerShell_finite_le_theta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBufferedInnerShell_finite_le_theta_eq
  {k m : Nat}
  {q beta : Real}
-- given
  (hk : 1 ≤ k)
  (hkm : 2 * k < m)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  (triangular.wiredBufferedMeasure m (by rw [sub_pos] exact Real.exp_lt_one_iff.mpr (by linarith)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (triangular.bufferedCylinder (2 * k) (triangularBufferedInnerShellEvent k)) ≤ triangularOuterInnerTheta q beta k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBufferedInnerShell_finite_le_theta k m hk hkm q beta hq hbeta

/--
[triangularBufferedInnerShell_infinite_le_theta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBufferedInnerShell_infinite_le_theta_eq
  {k : Nat}
  {q beta : Real}
-- given
  (hk : 1 ≤ k)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  (triangular.wiredBufferedInfiniteVolume (by rw [sub_pos] exact Real.exp_lt_one_iff.mpr (by linarith)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (triangular.bufferedCylinder (2 * k) (triangularBufferedInnerShellEvent k)) ≤ triangularOuterInnerTheta q beta k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBufferedInnerShell_infinite_le_theta k hk q beta hq hbeta

/--
[triangular_root_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangular_root_eq_zero_eq :
-- imply
  triangular.root = (0 : Site 2) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_root_eq_zero

/--
[triangular_percolationEvent_subset_innerShell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangular_percolationEvent_subset_innerShell_eq
  {k : Nat}
-- given
  (hk : 1 ≤ k) :
-- imply
  triangular.percolationEvent ⊆ triangular.bufferedCylinder (2 * k) (triangularBufferedInnerShellEvent k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_percolationEvent_subset_innerShell k hk

/--
[triangular_wiredPercolationProbability_le_theta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangular_wiredPercolationProbability_le_theta_eq
  {k : Nat}
  {q beta : Real}
-- given
  (hk : 1 ≤ k)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  triangular.wiredPercolationProbability (1 - Real.exp (-beta)) q ≤ triangularOuterInnerTheta q beta k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_wiredPercolationProbability_le_theta k hk q beta hq hbeta

/--
[triangularBufferedToBox_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBufferedToBox_injective_eq
  {j N : Nat}
-- given
  (hjn : triangular.bufferedRadius j ≤ 2 * N) :
-- imply
  Function.Injective (triangularBufferedToBox j N hjn) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBufferedToBox_injective j N hjn

/--
[triangularBufferedToBox_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBufferedToBox_adjMatch_eq
  {j N : Nat}
-- given
  (hjn : triangular.bufferedRadius j ≤ 2 * N) :
-- imply
  ocd_AdjMatch (triangular.bufferedGraph j) (triangularBoxGraph (2 * N)) (triangularBufferedToBox j N hjn) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBufferedToBox_adjMatch j N hjn

/--
[triangularBufferedToBox_not_outerBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBufferedToBox_not_outerBoundary_eq
  {j N : Nat}
  {x : triangular.BufferedVertex j}
-- given
  (hjn : triangular.bufferedRadius j < N) :
-- imply
  triangularBufferedToBox j N (by omega) x ∉ triangularBoxShell (2 * N) (2 * N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBufferedToBox_not_outerBoundary j N hjn x

/--
[triangularBufferedToBox_inducedWiring_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBufferedToBox_inducedWiring_le_eq
  {j N : Nat}
  {psi : ConfigSpace (Sym2 (TriangularBoxVertex (2 * N)))}
-- given
  (hjn : triangular.bufferedRadius j < N) :
-- imply
  ocd_inducedWiring (triangularBoxGraph (2 * N)) (triangularBufferedToBox j N (by omega)) (fun y => y ∈ triangularBoxShell (2 * N) (2 * N)) psi ≤ boundaryCliqueGraph (triangular.bufferedBoundary j) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBufferedToBox_inducedWiring_le j N hjn psi

/--
[triangularCenteredShellFullEvent_subset_bufferedRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularCenteredShellFullEvent_subset_bufferedRestrict_eq
  {j N : Nat}
-- given
  (hjn : triangular.bufferedRadius j < N) :
-- imply
  triangularCenteredShellFullEvent (2 * N) N ⊆ ocd_innerRestrict (triangularBufferedToBox j N (by omega)) ⁻¹' triangular.bufferedRootBoundaryEvent j := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularCenteredShellFullEvent_subset_bufferedRestrict j N hjn

/--
[triangularOuterInnerTheta_le_bufferedRootArmMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularOuterInnerTheta_le_bufferedRootArmMass_eq
  {j N : Nat}
  {q beta : Real}
-- given
  (hjn : triangular.bufferedRadius j < N)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  triangularOuterInnerTheta q beta N ≤ triangularBufferedRootArmMass j (1 - Real.exp (-beta)) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularOuterInnerTheta_le_bufferedRootArmMass j N hjn q beta hq hbeta

/--
[triangularBufferedRestrictLE_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBufferedRestrictLE_self_eq
  {j : Nat}
  {omega : ConfigSpace (Sym2 (triangular.BufferedVertex j))} :
-- imply
  triangular.bufferedRestrictLE (le_refl j) omega = omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBufferedRestrictLE_self j omega

/--
[triangularBufferedRootArmMass_eq_measure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBufferedRootArmMass_eq_measure_eq
  {j : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  triangularBufferedRootArmMass j p q = (triangular.wiredBufferedMeasure j hp hp1 hq : Measure (ConfigSpace (Sym2 (Site 2)))).real (triangular.bufferedCylinder j (triangular.bufferedRootBoundaryEvent j)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBufferedRootArmMass_eq_measure j hp hp1 hq

/--
[triangularBufferedRootArmMass_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBufferedRootArmMass_tendsto_eq
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun j => triangularBufferedRootArmMass j p q) atTop (nhds (triangular.wiredPercolationProbability p q)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBufferedRootArmMass_tendsto hp hp1 hq

/--
[triangularOuterInnerTheta_tendsto_percolation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularOuterInnerTheta_tendsto_percolation_eq
  {q beta : Real}
-- given
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  Tendsto (fun n => triangularOuterInnerTheta q beta n) atTop (nhds (triangular.wiredPercolationProbability (1 - Real.exp (-beta)) q)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularOuterInnerTheta_tendsto_percolation q beta hq hbeta

/--
[triangularCriticalBeta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularCriticalBeta_pos_eq
  {q : Real}
-- given
  (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
-- imply
  0 < triangularCriticalBeta q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularCriticalBeta_pos q hpc

/--
[triangularCriticalBeta_param](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularCriticalBeta_param_eq
  {q : Real}
-- given
  (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
-- imply
  1 - Real.exp (-triangularCriticalBeta q) = triangular.criticalPoint q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularCriticalBeta_param q hpc

/--
[betaToP_lt_triangularCritical_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma betaToP_lt_triangularCritical_of_lt_eq
  {q : Real}
  {beta : Real}
-- given
  (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
  (hbeta : beta < triangularCriticalBeta q) :
-- imply
  1 - Real.exp (-beta) < triangular.criticalPoint q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.betaToP_lt_triangularCritical_of_lt q hpc hbeta

/--
[triangularCritical_lt_betaToP_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularCritical_lt_betaToP_of_lt_eq
  {q : Real}
  {beta : Real}
-- given
  (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
  (hbeta : triangularCriticalBeta q < beta) :
-- imply
  triangular.criticalPoint q < 1 - Real.exp (-beta) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularCritical_lt_betaToP_of_lt q hpc hbeta

/--
[triangularNormalizedTheta_tendsto_percolation_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularNormalizedTheta_tendsto_percolation_div_eq
  {q beta0 beta : Real}
-- given
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  Tendsto (fun n => triangularNormalizedTheta q beta0 n beta) atTop (nhds (triangular.wiredPercolationProbability (1 - Real.exp (-beta)) q / triangularSharpConstant beta0)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularNormalizedTheta_tendsto_percolation_div q beta0 beta hq hbeta

/--
[triangularThresholdSet_mem_of_percolation_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularThresholdSet_mem_of_percolation_pos_eq
  {q beta0 beta : Real}
-- given
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hperc : 0 < triangular.wiredPercolationProbability (1 - Real.exp (-beta)) q) :
-- imply
  beta ∈ BetaThresholdBound.thresholdSet (fun b n => IntegrationSubcritical.Sig (triangularThresholdTheta q beta0) n b) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularThresholdSet_mem_of_percolation_pos q beta0 beta hq hbeta hperc

/--
[triangularThresholdSet_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularThresholdSet_nonempty_eq
  {q beta0 : Real}
-- given
  (hq : 1 ≤ q)
  (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
-- imply
  (BetaThresholdBound.thresholdSet (fun b n => IntegrationSubcritical.Sig (triangularThresholdTheta q beta0) n b)).Nonempty := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularThresholdSet_nonempty q beta0 hq hpc

/--
[triangularBeta1_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBeta1_nonneg_eq
  {q beta0 : Real}
-- given
  (hq : 1 ≤ q)
  (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
-- imply
  0 ≤ triangularBeta1 q beta0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBeta1_nonneg q beta0 hq hpc

/--
[triangularThresholdLogRatio_bddAbove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularThresholdLogRatio_bddAbove_eq
  {q beta0 beta : Real}
-- given
  (hq : 1 ≤ q)
  (hbeta0 : 0 ≤ beta0) :
-- imply
  IsBoundedUnder (· ≤ ·) atTop (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig (triangularThresholdTheta q beta0) n beta)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularThresholdLogRatio_bddAbove q beta0 beta hq hbeta0

/--
[triangularThresholdLogRatio_cobounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularThresholdLogRatio_cobounded_eq
  {q beta0 beta : Real}
-- given
  (hq : 1 ≤ q)
  (hbeta0 : 0 ≤ beta0) :
-- imply
  IsCoboundedUnder (· ≤ ·) atTop (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig (triangularThresholdTheta q beta0) n beta)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularThresholdLogRatio_cobounded q beta0 beta hq hbeta0

/--
[triangularPercolation_difference_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularPercolation_difference_lower_eq
  {q beta0 beta' beta : Real}
-- given
  (hq : 1 ≤ q)
  (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
  (hcrit : triangularBeta1 q beta0 < beta')
  (hbeta : beta' ≤ beta)
  (hupper : beta ≤ beta0) :
-- imply
  beta - beta' ≤ triangular.wiredPercolationProbability (1 - Real.exp (-beta)) q / triangularSharpConstant beta0 - triangular.wiredPercolationProbability (1 - Real.exp (-beta')) q / triangularSharpConstant beta0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularPercolation_difference_lower q beta0 beta' beta hq hpc hcrit hbeta hupper

/--
[triangularPercolation_meanField_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularPercolation_meanField_lower_eq
  {q beta0 beta : Real}
-- given
  (hq : 1 ≤ q)
  (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
  (hcrit : triangularBeta1 q beta0 < beta)
  (hupper : beta ≤ beta0) :
-- imply
  triangularSharpConstant beta0 * (beta - triangularBeta1 q beta0) ≤ triangular.wiredPercolationProbability (1 - Real.exp (-beta)) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularPercolation_meanField_lower q beta0 beta hq hpc hcrit hupper

/--
[triangularBeta1_eq_criticalBeta_of_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBeta1_eq_criticalBeta_of_ge_eq
  {q beta0 : Real}
-- given
  (hq : 1 ≤ q)
  (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
  (hbeta0 : triangularCriticalBeta q ≤ beta0) :
-- imply
  triangularBeta1 q beta0 = triangularCriticalBeta q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBeta1_eq_criticalBeta_of_ge q beta0 hq hpc hbeta0

/--
[triangularOuterInner_exponential_decay_below_critical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularOuterInner_exponential_decay_below_critical_eq
  {q beta : Real}
-- given
  (hq : 1 ≤ q)
  (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
  (hbeta : 0 < beta)
  (hsub : beta < triangularCriticalBeta q) :
-- imply
  ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 ≤ n → triangularOuterInnerTheta q beta n ≤ Real.exp (-((n : Real) / Q * ((triangularCriticalBeta q - beta) / 4))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularOuterInner_exponential_decay_below_critical q beta hq hpc hbeta hsub

/--
[triangularTransBox_mem_bufferLevel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularTransBox_mem_bufferLevel_eq
  {k : Nat}
  {x : Site 2}
  {y : TriangularTransBoxVertex (2 * k) x} :
-- imply
  y.1 ∈ box 2 (triangularTransBufferLevel k x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransBox_mem_bufferLevel k x y

/--
[triangularTransBoxToBuffered_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularTransBoxToBuffered_injective_eq
  {k : Nat}
  {x : Site 2} :
-- imply
  Function.Injective (triangularTransBoxToBuffered k x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransBoxToBuffered_injective k x

/--
[triangularTransBoxToBufferedAt_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularTransBoxToBufferedAt_injective_eq
  {k : Nat}
  {x : Site 2}
  {m : Nat}
-- given
  (hm : triangularTransBufferLevel k x ≤ m) :
-- imply
  Function.Injective (triangularTransBoxToBufferedAt k x m hm) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransBoxToBufferedAt_injective k x m hm

/--
[triangularTransBoxToBufferedAt_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularTransBoxToBufferedAt_adjMatch_eq
  {k : Nat}
  {x : Site 2}
  {m : Nat}
-- given
  (hm : triangularTransBufferLevel k x ≤ m) :
-- imply
  ocd_AdjMatch (triangularTransBoxGraph (2 * k) x) (triangular.bufferedGraph m) (triangularTransBoxToBufferedAt k x m hm) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransBoxToBufferedAt_adjMatch k x m hm

/--
[triangularTransBoxToBufferedAt_inducedWiring_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularTransBoxToBufferedAt_inducedWiring_le_eq
  {k : Nat}
  {x : Site 2}
  {m : Nat}
  {psi : ConfigSpace (Sym2 (triangular.BufferedVertex m))}
-- given
  (hk : 1 ≤ k)
  (hm : triangularTransBufferLevel k x < m) :
-- imply
  ocd_inducedWiring (triangular.bufferedGraph m) (triangularTransBoxToBufferedAt k x m hm.le) (triangular.bufferedBoundary m) psi ≤ boundaryCliqueGraph (triangularTransBoxBoundary (2 * k) x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransBoxToBufferedAt_inducedWiring_le k hk x m hm psi

/--
[triangularTransShellFullEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularTransShellFullEvent_increasing_eq
  {R k : Nat}
  {x : Site 2} :
-- imply
  IsIncreasing (triangularTransShellFullEvent R k x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransShellFullEvent_increasing R k x

/--
[triangularBufferedTransShellEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBufferedTransShellEvent_increasing_eq
  {k : Nat}
  {x : Site 2} :
-- imply
  IsIncreasing (triangularBufferedTransShellEvent k x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBufferedTransShellEvent_increasing k x

/--
[triangularTransFullMass_eq_outerInnerTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularTransFullMass_eq_outerInnerTheta_eq
  {k : Nat}
  {x : Site 2}
  {q beta : Real}
-- given
  (hk : 1 ≤ k)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  finiteWiredEventMass (triangularTransBoxGraph (2 * k) x) (triangularTransBoxBoundary (2 * k) x) (1 - Real.exp (-beta)) q (triangularTransShellFullEvent (2 * k) k x) = triangularOuterInnerTheta q beta k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransFullMass_eq_outerInnerTheta k hk x q beta hq hbeta

/--
[triangularBufferedTransShell_finite_le_theta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBufferedTransShell_finite_le_theta_eq
  {k : Nat}
  {x : Site 2}
  {m : Nat}
  {q beta : Real}
-- given
  (hk : 1 ≤ k)
  (hm : triangularTransBufferLevel k x < m)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  (triangular.wiredBufferedMeasure m (by rw [sub_pos] exact Real.exp_lt_one_iff.mpr (by linarith)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (triangular.bufferedCylinder (triangularTransBufferLevel k x) (triangularBufferedTransShellEvent k x)) ≤ triangularOuterInnerTheta q beta k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBufferedTransShell_finite_le_theta k hk x m hm q beta hq hbeta

/--
[triangularBufferedTransShell_infinite_le_theta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangularBufferedTransShell_infinite_le_theta_eq
  {k : Nat}
  {x : Site 2}
  {q beta : Real}
-- given
  (hk : 1 ≤ k)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  (triangular.wiredBufferedInfiniteVolume (by rw [sub_pos] exact Real.exp_lt_one_iff.mpr (by linarith)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (triangular.bufferedCylinder (triangularTransBufferLevel k x) (triangularBufferedTransShellEvent k x)) ≤ triangularOuterInnerTheta q beta k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBufferedTransShell_infinite_le_theta k hk x q beta hq hbeta

/--
[triangular_twoPointEvent_subset_transShell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangular_twoPointEvent_subset_transShell_eq
  {k : Nat}
  {x y : Site 2}
-- given
  (hk : 1 ≤ k)
  (hxy : k ≤ centeredRadius x y) :
-- imply
  triangular.twoPointEvent x y ⊆ triangular.bufferedCylinder (triangularTransBufferLevel k x) (triangularBufferedTransShellEvent k x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_twoPointEvent_subset_transShell k hk x y hxy

/--
[triangular_wiredTwoPointProbability_le_theta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangular_wiredTwoPointProbability_le_theta_eq
  {k : Nat}
  {x y : Site 2}
  {q beta : Real}
-- given
  (hk : 1 ≤ k)
  (hxy : k ≤ centeredRadius x y)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  triangular.wiredTwoPointProbability (1 - Real.exp (-beta)) q x y ≤ triangularOuterInnerTheta q beta k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_wiredTwoPointProbability_le_theta k hk x y hxy q beta hq hbeta

/--
[betaOfP_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma betaOfP_pos_eq
  {p : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  0 < -Real.log (1 - p) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.betaOfP_pos hp hp1

/--
[betaOfP_param](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma betaOfP_param_eq
  {p : Real}
-- given
  (hp1 : p < 1) :
-- imply
  1 - Real.exp (-(-Real.log (1 - p))) = p := by
-- proof
  apply StatMech.FK.PeriodicPlanar.betaOfP_param hp1

/--
[betaOfP_lt_criticalBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma betaOfP_lt_criticalBeta_eq
  {q p : Real}
-- given
  (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
  (hp1 : p < 1)
  (hsub : p < triangular.criticalPoint q) :
-- imply
  -Real.log (1 - p) < triangularCriticalBeta q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.betaOfP_lt_criticalBeta q p hpc hp1 hsub

/--
[centeredRadius_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma centeredRadius_eq_zero_iff_eq
  {x y : Site 2} :
-- imply
  centeredRadius x y = 0 ↔ x = y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.centeredRadius_eq_zero_iff x y

/--
[triangular_subcritical_twoPoint_exponential_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean)
-/
@[path]
private lemma triangular_subcritical_twoPoint_exponential_decay_eq
  {q : Real}
-- given
  (hq : 1 ≤ q)
  (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
-- imply
  SubcriticalTwoPointExponentialDecay triangular q (triangular.criticalPoint q) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_subcritical_twoPoint_exponential_decay q hq hpc


-- created on 2026-10-23
