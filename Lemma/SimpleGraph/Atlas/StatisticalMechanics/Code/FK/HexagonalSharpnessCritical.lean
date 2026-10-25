import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessCritical.Part7
open Finset Set Filter Topology MeasureTheory SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[hexagonalBoxToBuffered_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBoxToBuffered_injective_eq
  {k : Nat} :
-- imply
  Function.Injective (hexagonalBoxToBuffered k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBoxToBuffered_injective k

/--
[hexagonalBoxToBuffered_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBoxToBuffered_adjMatch_eq
  {k : Nat} :
-- imply
  ocd_AdjMatch (hexagonalBoxGraph (2 * k)) (hexagonal.bufferedGraph (2 * k)) (hexagonalBoxToBuffered k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBoxToBuffered_adjMatch k

/--
[hexagonalCenteredShellFullEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalCenteredShellFullEvent_increasing_eq
  {R k : Nat} :
-- imply
  IsIncreasing (hexagonalCenteredShellFullEvent R k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalCenteredShellFullEvent_increasing R k

/--
[hexagonalBufferedInnerShellEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBufferedInnerShellEvent_increasing_eq
  {k : Nat} :
-- imply
  IsIncreasing (hexagonalBufferedInnerShellEvent k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBufferedInnerShellEvent_increasing k

/--
[hexagonalBoxToBufferedAt_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBoxToBufferedAt_injective_eq
  {k m : Nat}
-- given
  (hkm : 2 * k ≤ hexagonal.bufferedRadius m) :
-- imply
  Function.Injective (hexagonalBoxToBufferedAt k m hkm) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBoxToBufferedAt_injective k m hkm

/--
[hexagonalBoxToBufferedAt_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBoxToBufferedAt_adjMatch_eq
  {k m : Nat}
-- given
  (hkm : 2 * k ≤ hexagonal.bufferedRadius m) :
-- imply
  ocd_AdjMatch (hexagonalBoxGraph (2 * k)) (hexagonal.bufferedGraph m) (hexagonalBoxToBufferedAt k m hkm) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBoxToBufferedAt_adjMatch k m hkm

/--
[hexagonalBoxToBufferedAt_not_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBoxToBufferedAt_not_boundary_eq
  {k m : Nat}
  {x : HexagonalBoxVertex (2 * k)}
-- given
  (hkm : 2 * k < m) :
-- imply
  ¬ hexagonal.bufferedBoundary m (hexagonalBoxToBufferedAt k m ((hexagonal.id_le_bufferedRadius (2 * k)).trans (hexagonal.bufferedRadius_strictMono.monotone hkm.le)) x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBoxToBufferedAt_not_boundary k m hkm x

/--
[hexagonalBoxToBufferedAt_boundary_of_adj_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBoxToBufferedAt_boundary_of_adj_outside_eq
  {k : Nat}
  {x : HexagonalBoxVertex (2 * k)}
  {z : HexVertex}
-- given
  (hk : 1 ≤ k)
  (hxz : hexagonalGraph.Adj x.1 z)
  (hz : z.1 ∉ box 2 (2 * k)) :
-- imply
  x ∈ hexagonalBoxShell (2 * k) (2 * k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBoxToBufferedAt_boundary_of_adj_outside k hk x z hxz hz

/--
[hexagonalBoxToBufferedAt_inducedWiring_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBoxToBufferedAt_inducedWiring_le_eq
  {k m : Nat}
  {psi : ConfigSpace (Sym2 (hexagonal.BufferedVertex m))}
-- given
  (hk : 1 ≤ k)
  (hkm : 2 * k < m) :
-- imply
  ocd_inducedWiring (hexagonal.bufferedGraph m) (hexagonalBoxToBufferedAt k m ((hexagonal.id_le_bufferedRadius (2 * k)).trans (hexagonal.bufferedRadius_strictMono.monotone hkm.le))) (hexagonal.bufferedBoundary m) psi ≤ boundaryCliqueGraph (fun x => x ∈ hexagonalBoxShell (2 * k) (2 * k)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBoxToBufferedAt_inducedWiring_le k m hk hkm psi

/--
[hexagonalBufferedInnerShell_finite_le_theta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBufferedInnerShell_finite_le_theta_eq
  {k m : Nat}
  {q beta : Real}
-- given
  (hk : 1 ≤ k)
  (hkm : 2 * k < m)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  (hexagonal.wiredBufferedMeasure m (by rw [sub_pos] exact Real.exp_lt_one_iff.mpr (by linarith)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real (hexagonal.bufferedCylinder (2 * k) (hexagonalBufferedInnerShellEvent k)) ≤ hexagonalOuterInnerTheta q beta k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBufferedInnerShell_finite_le_theta k m hk hkm q beta hq hbeta

/--
[hexagonalBufferedInnerShell_infinite_le_theta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBufferedInnerShell_infinite_le_theta_eq
  {k : Nat}
  {q beta : Real}
-- given
  (hk : 1 ≤ k)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  (hexagonal.wiredBufferedInfiniteVolume (by rw [sub_pos] exact Real.exp_lt_one_iff.mpr (by linarith)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real (hexagonal.bufferedCylinder (2 * k) (hexagonalBufferedInnerShellEvent k)) ≤ hexagonalOuterInnerTheta q beta k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBufferedInnerShell_infinite_le_theta k hk q beta hq hbeta

/--
[hexagonal_root_coord_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonal_root_coord_eq_zero_eq :
-- imply
  hexagonal.root.1 = (0 : Site 2) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_root_coord_eq_zero

/--
[site_neg_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma site_neg_mem_box_eq
  {n : Nat}
  {x : Site 2}
-- given
  (hx : x ∈ box 2 n) :
-- imply
  -x ∈ box 2 n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.site_neg_mem_box hx

/--
[hexagonalRootFrame_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalRootFrame_adj_eq
  {u v : HexVertex} :
-- imply
  hexagonalGraph.Adj (hexagonalRootFrame u) (hexagonalRootFrame v) ↔ hexagonalGraph.Adj u v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalRootFrame_adj u v

/--
[hexagonalRootFrame_coord_mem_box_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalRootFrame_coord_mem_box_iff_eq
  {n : Nat}
  {v : HexVertex} :
-- imply
  (hexagonalRootFrame v).1 ∈ box 2 n ↔ v.1 ∈ box 2 n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalRootFrame_coord_mem_box_iff n v

/--
[hexagonalRootFrame_mem_orbitBox_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalRootFrame_mem_orbitBox_iff_eq
  {n : Nat}
  {v : HexVertex} :
-- imply
  hexagonalRootFrame v ∈ hexagonal.orbitBox n ↔ v ∈ hexagonal.orbitBox n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalRootFrame_mem_orbitBox_iff n v

/--
[hexagonalRootFrame_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalRootFrame_root_eq :
-- imply
  hexagonalRootFrame hexagonal.root = ((0, false) : HexVertex) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalRootFrame_root

/--
[hexagonal_percolationEvent_subset_innerShell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonal_percolationEvent_subset_innerShell_eq
  {k : Nat}
-- given
  (hk : 1 ≤ k) :
-- imply
  hexagonal.percolationEvent ⊆ hexagonal.bufferedCylinder (hexagonalTransBufferLevel k hexagonal.root.1) (hexagonalBufferedTransShellEvent k hexagonal.root) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_percolationEvent_subset_innerShell k hk

/--
[hexagonal_wiredPercolationProbability_le_theta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonal_wiredPercolationProbability_le_theta_eq
  {k : Nat}
  {q beta : Real}
-- given
  (hk : 1 ≤ k)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  hexagonal.wiredPercolationProbability (1 - Real.exp (-beta)) q ≤ hexagonalOuterInnerTheta q beta k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_wiredPercolationProbability_le_theta k hk q beta hq hbeta

/--
[hexagonalBufferedToBox_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBufferedToBox_injective_eq
  {j N : Nat}
-- given
  (hjn : hexagonal.bufferedRadius j ≤ 2 * N) :
-- imply
  Function.Injective (hexagonalBufferedToBox j N hjn) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBufferedToBox_injective j N hjn

/--
[hexagonalBufferedToBox_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBufferedToBox_adjMatch_eq
  {j N : Nat}
-- given
  (hjn : hexagonal.bufferedRadius j ≤ 2 * N) :
-- imply
  ocd_AdjMatch (hexagonal.bufferedGraph j) (hexagonalBoxGraph (2 * N)) (hexagonalBufferedToBox j N hjn) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBufferedToBox_adjMatch j N hjn

/--
[hexagonalBufferedToBox_not_outerBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBufferedToBox_not_outerBoundary_eq
  {j N : Nat}
  {x : hexagonal.BufferedVertex j}
-- given
  (hjn : hexagonal.bufferedRadius j < N) :
-- imply
  hexagonalBufferedToBox j N (by omega) x ∉ hexagonalBoxShell (2 * N) (2 * N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBufferedToBox_not_outerBoundary j N hjn x

/--
[hexagonalBufferedToBox_inducedWiring_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBufferedToBox_inducedWiring_le_eq
  {j N : Nat}
  {psi : ConfigSpace (Sym2 (HexagonalBoxVertex (2 * N)))}
-- given
  (hjn : hexagonal.bufferedRadius j < N) :
-- imply
  ocd_inducedWiring (hexagonalBoxGraph (2 * N)) (hexagonalBufferedToBox j N (by omega)) (fun y => y ∈ hexagonalBoxShell (2 * N) (2 * N)) psi ≤ boundaryCliqueGraph (hexagonal.bufferedBoundary j) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBufferedToBox_inducedWiring_le j N hjn psi

/--
[hexagonalCenteredShellFullEvent_subset_bufferedRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalCenteredShellFullEvent_subset_bufferedRestrict_eq
  {j N : Nat}
-- given
  (hjn : hexagonal.bufferedRadius j < N) :
-- imply
  hexagonalCenteredShellFullEvent (2 * N) N ⊆ ocd_innerRestrict (hexagonalBufferedToBox j N (by omega)) ⁻¹' hexagonal.bufferedRootBoundaryEvent j := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalCenteredShellFullEvent_subset_bufferedRestrict j N hjn

/--
[hexagonalOuterInnerTheta_le_bufferedRootArmMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalOuterInnerTheta_le_bufferedRootArmMass_eq
  {j N : Nat}
  {q beta : Real}
-- given
  (hjn : hexagonal.bufferedRadius j < N)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  hexagonalOuterInnerTheta q beta N ≤ hexagonalBufferedRootArmMass j (1 - Real.exp (-beta)) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalOuterInnerTheta_le_bufferedRootArmMass j N hjn q beta hq hbeta

/--
[hexagonalBufferedRestrictLE_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBufferedRestrictLE_self_eq
  {j : Nat}
  {omega : ConfigSpace (Sym2 (hexagonal.BufferedVertex j))} :
-- imply
  hexagonal.bufferedRestrictLE (le_refl j) omega = omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBufferedRestrictLE_self j omega

/--
[hexagonalBufferedRootArmMass_eq_measure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBufferedRootArmMass_eq_measure_eq
  {j : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  hexagonalBufferedRootArmMass j p q = (hexagonal.wiredBufferedMeasure j hp hp1 hq : Measure (ConfigSpace (Sym2 HexVertex))).real (hexagonal.bufferedCylinder j (hexagonal.bufferedRootBoundaryEvent j)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBufferedRootArmMass_eq_measure j hp hp1 hq

/--
[hexagonalBufferedRootArmMass_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBufferedRootArmMass_tendsto_eq
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun j => hexagonalBufferedRootArmMass j p q) atTop (nhds (hexagonal.wiredPercolationProbability p q)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBufferedRootArmMass_tendsto hp hp1 hq

/--
[hexagonalOuterInnerTheta_tendsto_percolation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalOuterInnerTheta_tendsto_percolation_eq
  {q beta : Real}
-- given
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  Tendsto (fun n => hexagonalOuterInnerTheta q beta n) atTop (nhds (hexagonal.wiredPercolationProbability (1 - Real.exp (-beta)) q)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalOuterInnerTheta_tendsto_percolation q beta hq hbeta

/--
[hexagonalCriticalBeta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalCriticalBeta_pos_eq
  {q : Real}
-- given
  (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
-- imply
  0 < hexagonalCriticalBeta q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalCriticalBeta_pos q hpc

/--
[hexagonalCriticalBeta_param](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalCriticalBeta_param_eq
  {q : Real}
-- given
  (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
-- imply
  1 - Real.exp (-hexagonalCriticalBeta q) = hexagonal.criticalPoint q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalCriticalBeta_param q hpc

/--
[betaToP_lt_hexagonalCritical_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma betaToP_lt_hexagonalCritical_of_lt_eq
  {q : Real}
  {beta : Real}
-- given
  (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
  (hbeta : beta < hexagonalCriticalBeta q) :
-- imply
  1 - Real.exp (-beta) < hexagonal.criticalPoint q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.betaToP_lt_hexagonalCritical_of_lt q hpc hbeta

/--
[hexagonalCritical_lt_betaToP_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalCritical_lt_betaToP_of_lt_eq
  {q : Real}
  {beta : Real}
-- given
  (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
  (hbeta : hexagonalCriticalBeta q < beta) :
-- imply
  hexagonal.criticalPoint q < 1 - Real.exp (-beta) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalCritical_lt_betaToP_of_lt q hpc hbeta

/--
[hexagonalNormalizedTheta_tendsto_percolation_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalNormalizedTheta_tendsto_percolation_div_eq
  {q beta0 beta : Real}
-- given
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  Tendsto (fun n => hexagonalNormalizedTheta q beta0 n beta) atTop (nhds (hexagonal.wiredPercolationProbability (1 - Real.exp (-beta)) q / hexagonalSharpConstant beta0)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalNormalizedTheta_tendsto_percolation_div q beta0 beta hq hbeta

/--
[hexagonalThresholdSet_mem_of_percolation_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalThresholdSet_mem_of_percolation_pos_eq
  {q beta0 beta : Real}
-- given
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hperc : 0 < hexagonal.wiredPercolationProbability (1 - Real.exp (-beta)) q) :
-- imply
  beta ∈ BetaThresholdBound.thresholdSet (fun b n => IntegrationSubcritical.Sig (hexagonalThresholdTheta q beta0) n b) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalThresholdSet_mem_of_percolation_pos q beta0 beta hq hbeta hperc

/--
[hexagonalThresholdSet_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalThresholdSet_nonempty_eq
  {q beta0 : Real}
-- given
  (hq : 1 ≤ q)
  (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
-- imply
  (BetaThresholdBound.thresholdSet (fun b n => IntegrationSubcritical.Sig (hexagonalThresholdTheta q beta0) n b)).Nonempty := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalThresholdSet_nonempty q beta0 hq hpc

/--
[hexagonalBeta1_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBeta1_nonneg_eq
  {q beta0 : Real}
-- given
  (hq : 1 ≤ q)
  (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
-- imply
  0 ≤ hexagonalBeta1 q beta0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBeta1_nonneg q beta0 hq hpc

/--
[hexagonalThresholdLogRatio_bddAbove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalThresholdLogRatio_bddAbove_eq
  {q beta0 beta : Real}
-- given
  (hq : 1 ≤ q)
  (hbeta0 : 0 ≤ beta0) :
-- imply
  IsBoundedUnder (· ≤ ·) atTop (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig (hexagonalThresholdTheta q beta0) n beta)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalThresholdLogRatio_bddAbove q beta0 beta hq hbeta0

/--
[hexagonalThresholdLogRatio_cobounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalThresholdLogRatio_cobounded_eq
  {q beta0 beta : Real}
-- given
  (hq : 1 ≤ q)
  (hbeta0 : 0 ≤ beta0) :
-- imply
  IsCoboundedUnder (· ≤ ·) atTop (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig (hexagonalThresholdTheta q beta0) n beta)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalThresholdLogRatio_cobounded q beta0 beta hq hbeta0

/--
[hexagonalPercolation_difference_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalPercolation_difference_lower_eq
  {q beta0 beta' beta : Real}
-- given
  (hq : 1 ≤ q)
  (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
  (hcrit : hexagonalBeta1 q beta0 < beta')
  (hbeta : beta' ≤ beta)
  (hupper : beta ≤ beta0) :
-- imply
  beta - beta' ≤ hexagonal.wiredPercolationProbability (1 - Real.exp (-beta)) q / hexagonalSharpConstant beta0 - hexagonal.wiredPercolationProbability (1 - Real.exp (-beta')) q / hexagonalSharpConstant beta0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalPercolation_difference_lower q beta0 beta' beta hq hpc hcrit hbeta hupper

/--
[hexagonalPercolation_meanField_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalPercolation_meanField_lower_eq
  {q beta0 beta : Real}
-- given
  (hq : 1 ≤ q)
  (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
  (hcrit : hexagonalBeta1 q beta0 < beta)
  (hupper : beta ≤ beta0) :
-- imply
  hexagonalSharpConstant beta0 * (beta - hexagonalBeta1 q beta0) ≤ hexagonal.wiredPercolationProbability (1 - Real.exp (-beta)) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalPercolation_meanField_lower q beta0 beta hq hpc hcrit hupper

/--
[hexagonalBeta1_eq_criticalBeta_of_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBeta1_eq_criticalBeta_of_ge_eq
  {q beta0 : Real}
-- given
  (hq : 1 ≤ q)
  (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
  (hbeta0 : hexagonalCriticalBeta q ≤ beta0) :
-- imply
  hexagonalBeta1 q beta0 = hexagonalCriticalBeta q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBeta1_eq_criticalBeta_of_ge q beta0 hq hpc hbeta0

/--
[hexagonalOuterInner_exponential_decay_below_critical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalOuterInner_exponential_decay_below_critical_eq
  {q beta : Real}
-- given
  (hq : 1 ≤ q)
  (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
  (hbeta : 0 < beta)
  (hsub : beta < hexagonalCriticalBeta q) :
-- imply
  ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 ≤ n → hexagonalOuterInnerTheta q beta n ≤ Real.exp (-((n : Real) / Q * ((hexagonalCriticalBeta q - beta) / 4))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalOuterInner_exponential_decay_below_critical q beta hq hpc hbeta hsub

/--
[hexagonal_wiredTwoPointProbability_le_theta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonal_wiredTwoPointProbability_le_theta_eq
  {k : Nat}
  {x y : HexVertex}
  {q beta : Real}
-- given
  (hk : 1 ≤ k)
  (hxy : k ≤ centeredRadius x.1 y.1)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  hexagonal.wiredTwoPointProbability (1 - Real.exp (-beta)) q x y ≤ hexagonalOuterInnerTheta q beta k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_wiredTwoPointProbability_le_theta k hk x y hxy q beta hq hbeta

/--
[hexagonalBetaOfP_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBetaOfP_pos_eq
  {p : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  0 < -Real.log (1 - p) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBetaOfP_pos hp hp1

/--
[hexagonalBetaOfP_param](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBetaOfP_param_eq
  {p : Real}
-- given
  (hp1 : p < 1) :
-- imply
  1 - Real.exp (-(-Real.log (1 - p))) = p := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBetaOfP_param hp1

/--
[hexagonalBetaOfP_lt_criticalBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonalBetaOfP_lt_criticalBeta_eq
  {q p : Real}
-- given
  (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
  (hp1 : p < 1)
  (hsub : p < hexagonal.criticalPoint q) :
-- imply
  -Real.log (1 - p) < hexagonalCriticalBeta q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBetaOfP_lt_criticalBeta q p hpc hp1 hsub

/--
[hexagonal_centeredRadius_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonal_centeredRadius_eq_zero_iff_eq
  {x y : Site 2} :
-- imply
  centeredRadius x y = 0 ↔ x = y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_centeredRadius_eq_zero_iff x y

/--
[hexToTriAnchor_sub_mem_box_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexToTriAnchor_sub_mem_box_add_two_eq
  {x y : HexVertex}
  {r : Nat}
-- given
  (hxy : y.1 - x.1 ∈ box 2 r) :
-- imply
  hexToTriAnchor y - hexToTriAnchor x ∈ box 2 (r + 2) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexToTriAnchor_sub_mem_box_add_two hxy

/--
[hexagonal_subcritical_twoPoint_exponential_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean)
-/
@[path]
private lemma hexagonal_subcritical_twoPoint_exponential_decay_eq
  {q : Real}
-- given
  (hq : 1 ≤ q)
  (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
-- imply
  SubcriticalTwoPointExponentialDecay hexagonal q (hexagonal.criticalPoint q) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_subcritical_twoPoint_exponential_decay q hq hpc


-- created on 2026-10-23
