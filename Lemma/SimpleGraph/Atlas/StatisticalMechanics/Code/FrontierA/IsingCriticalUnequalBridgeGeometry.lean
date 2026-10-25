import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
open StatMech StatMech.FrontierA


/--
[oddPrismCentralInterfaceEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean)
-/
@[path]
private lemma oddPrismCentralInterfaceEdge_injective_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  Function.Injective (fun q : Fin (2 * n + 1) × Fin (2 * n + 1) => oddPrismCentralInterfaceEdge n hn q.1 q.2) := by
-- proof
  apply StatMech.FrontierA.oddPrismCentralInterfaceEdge_injective n hn

/--
[exists_cross_pair_of_mem_fis_interface](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean)
-/
@[path]
private lemma exists_cross_pair_of_mem_fis_interface_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {K : SimpleGraph (V ⊕ W)}
  [DecidableRel K.Adj]
  {e : Sym2 (V ⊕ W)}
-- given
  (hci : StatMech.FK.fis_CrossInterface G H K)
  (he : e ∈ StatMech.FK.fis_interface G H K) :
-- imply
  ∃ x : V, ∃ y : W, e = s(Sum.inl x, Sum.inr y) := by
-- proof
  apply StatMech.FrontierA.exists_cross_pair_of_mem_fis_interface G H K hci he

/--
[oddPrismCentralInterfaceEdge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean)
-/
@[path]
private lemma oddPrismCentralInterfaceEdge_mem_eq
  {n : Nat}
  {i j : Fin (2 * n + 1)}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismCentralInterfaceEdge n hn i j ∈ StatMech.FK.fis_interface (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n) (oddPrismUnequalGlueGraph n) := by
-- proof
  apply StatMech.FrontierA.oddPrismCentralInterfaceEdge_mem n hn i j

/--
[exists_oddPrismCentralInterfaceEdge_eq_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean)
-/
@[path]
private lemma exists_oddPrismCentralInterfaceEdge_eq_of_mem_eq
  {n : Nat}
  {e : Sym2 (OddPrismLowerBlockSite n ⊕ OddPrismUpperBlockSite n)}
-- given
  (hn : 0 < n)
  (he : e ∈ StatMech.FK.fis_interface (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n) (oddPrismUnequalGlueGraph n)) :
-- imply
  ∃ q : Fin (2 * n + 1) × Fin (2 * n + 1), e = oddPrismCentralInterfaceEdge n hn q.1 q.2 := by
-- proof
  apply StatMech.FrontierA.exists_oddPrismCentralInterfaceEdge_eq_of_mem n hn he

/--
[oddPrism_fis_interface_eq_central_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean)
-/
@[path]
private lemma oddPrism_fis_interface_eq_central_image_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  StatMech.FK.fis_interface (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n) (oddPrismUnequalGlueGraph n) = Finset.univ.image (fun q : Fin (2 * n + 1) × Fin (2 * n + 1) => oddPrismCentralInterfaceEdge n hn q.1 q.2) := by
-- proof
  apply StatMech.FrontierA.oddPrism_fis_interface_eq_central_image n hn

/--
[sum_oddPrism_fis_interface](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean)
-/
@[path]
private lemma sum_oddPrism_fis_interface_eq
  {n : Nat}
-- given
  (hn : 0 < n)
  (F : Sym2 (OddPrismLowerBlockSite n ⊕ OddPrismUpperBlockSite n) -> Real) :
-- imply
  (∑ e ∈ StatMech.FK.fis_interface (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n) (oddPrismUnequalGlueGraph n), F e) = ∑ q : Fin (2 * n + 1) × Fin (2 * n + 1), F (oddPrismCentralInterfaceEdge n hn q.1 q.2) := by
-- proof
  apply StatMech.FrontierA.sum_oddPrism_fis_interface n hn F

/--
[oddPrismUnequalBridgeMean_zero_eq_surfaceProductSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeMean_zero_eq_surfaceProductSum_eq
  {beta : Real}
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  unequalReplicaBridgeMean (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n) (oddPrismUnequalGlueGraph n) beta (fun v => beta * oddPrismPlusField n v.1) (fun v => beta * oddPrismPlusField n v.1) 0 = ∑ q : Fin (2 * n + 1) × Fin (2 * n + 1), expJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta) (fun v => beta * oddPrismPlusField n v.1) (fun a => spin a (oddPrismLowerHalfSurfaceSite n q.1 q.2)) * expJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta) (fun v => beta * oddPrismPlusField n v.1) (fun b => spin b (oddPrismUpperHalfSurfaceSite n hn q.1 q.2)) := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalBridgeMean_zero_eq_surfaceProductSum beta n hn

/--
[oddPrismLowerBlockSurfaceSpinMean_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean)
-/
@[path]
private lemma oddPrismLowerBlockSurfaceSpinMean_eq_eq
  {beta : Real}
  {n : Nat}
  {i j : Fin (2 * n + 1)} :
-- imply
  expJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta) (fun v => beta * oddPrismPlusField n v.1) (fun a => spin a (oddPrismLowerHalfSurfaceSite n i j)) = oddPrismLowerHalfSurfaceSpinMeanAt beta n i j := by
-- proof
  apply StatMech.FrontierA.oddPrismLowerBlockSurfaceSpinMean_eq beta n i j

/--
[oddPrismUpperBlockSurfaceSpinMean_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean)
-/
@[path]
private lemma oddPrismUpperBlockSurfaceSpinMean_nonneg_eq
  {beta : Real}
  {n : Nat}
  {i j : Fin (2 * n + 1)}
-- given
  (hbeta : 0 <= beta)
  (hn : 0 < n) :
-- imply
  0 <= expJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta) (fun v => beta * oddPrismPlusField n v.1) (fun b => spin b (oddPrismUpperHalfSurfaceSite n hn i j)) := by
-- proof
  apply StatMech.FrontierA.oddPrismUpperBlockSurfaceSpinMean_nonneg beta hbeta n hn i j

/--
[oddPrismUpperBlockSurfaceSpinMean_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean)
-/
@[path]
private lemma oddPrismUpperBlockSurfaceSpinMean_le_one_eq
  {beta : Real}
  {n : Nat}
  {i j : Fin (2 * n + 1)}
-- given
  (hn : 0 < n) :
-- imply
  expJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta) (fun v => beta * oddPrismPlusField n v.1) (fun b => spin b (oddPrismUpperHalfSurfaceSite n hn i j)) <= 1 := by
-- proof
  apply StatMech.FrontierA.oddPrismUpperBlockSurfaceSpinMean_le_one beta n hn i j

/--
[oddPrismUnequalBridgeMean_zero_le_surfaceSpinSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeMean_zero_le_surfaceSpinSum_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 <= beta)
  (hn : 0 < n) :
-- imply
  unequalReplicaBridgeMean (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n) (oddPrismUnequalGlueGraph n) beta (fun v => beta * oddPrismPlusField n v.1) (fun v => beta * oddPrismPlusField n v.1) 0 <= ∑ q : Fin (2 * n + 1) × Fin (2 * n + 1), oddPrismLowerHalfSurfaceSpinMeanAt beta n q.1 q.2 := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalBridgeMean_zero_le_surfaceSpinSum beta hbeta n hn

/--
[oddPrismCriticalLowerHalfSpinAverage_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean)
-/
@[path]
private lemma oddPrismCriticalLowerHalfSpinAverage_nonneg_eq
  {n : Nat} :
-- imply
  0 <= oddPrismCriticalLowerHalfSpinAverage n := by
-- proof
  apply StatMech.FrontierA.oddPrismCriticalLowerHalfSpinAverage_nonneg n

/--
[oddPrismCriticalLowerHalfSpinAverage_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean)
-/
@[path]
private lemma oddPrismCriticalLowerHalfSpinAverage_sq_le_eq
  {n : Nat} :
-- imply
  oddPrismCriticalLowerHalfSpinAverage n ^ 2 <= oddPrismCriticalLowerHalfSpinSquareAverage n := by
-- proof
  apply StatMech.FrontierA.oddPrismCriticalLowerHalfSpinAverage_sq_le n

/--
[oddPrismCriticalLowerHalfSpinAverage_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean)
-/
@[path]
private lemma oddPrismCriticalLowerHalfSpinAverage_tendsto_zero_eq :
-- imply
  Tendsto oddPrismCriticalLowerHalfSpinAverage atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.oddPrismCriticalLowerHalfSpinAverage_tendsto_zero

/--
[oddPrismCriticalUnequalBridgeMeanDensity_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean)
-/
@[path]
private lemma oddPrismCriticalUnequalBridgeMeanDensity_nonneg_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  0 <= oddPrismCriticalUnequalBridgeMeanDensity n := by
-- proof
  apply StatMech.FrontierA.oddPrismCriticalUnequalBridgeMeanDensity_nonneg n hn

/--
[oddPrismCriticalUnequalBridgeMeanDensity_le_lowerAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean)
-/
@[path]
private lemma oddPrismCriticalUnequalBridgeMeanDensity_le_lowerAverage_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  oddPrismCriticalUnequalBridgeMeanDensity n <= oddPrismCriticalLowerHalfSpinAverage n := by
-- proof
  apply StatMech.FrontierA.oddPrismCriticalUnequalBridgeMeanDensity_le_lowerAverage n hn

/--
[oddPrismCriticalUnequalBridgeMeanDensity_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean)
-/
@[path]
private lemma oddPrismCriticalUnequalBridgeMeanDensity_tendsto_zero_eq :
-- imply
  Tendsto oddPrismCriticalUnequalBridgeMeanDensity atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.oddPrismCriticalUnequalBridgeMeanDensity_tendsto_zero

/--
[standardCubicInterfaceDensity_critical_le_unequalMeanDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean)
-/
@[path]
private lemma standardCubicInterfaceDensity_critical_le_unequalMeanDensity_eq
  {n : Nat}
-- given
  (hn : 0 < n)
  (hvar : OddPrismUnequalBridgeVarianceOrder (Ising.betaC 3) n) :
-- imply
  standardCubicInterfaceDensity (Ising.betaC 3) n <= 2 * Ising.betaC 3 * oddPrismCriticalUnequalBridgeMeanDensity n := by
-- proof
  apply StatMech.FrontierA.standardCubicInterfaceDensity_critical_le_unequalMeanDensity n hn hvar

/--
[standardCubicInterfaceDensity_critical_tendsto_zero_of_varianceOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean)
-/
@[path]
private lemma standardCubicInterfaceDensity_critical_tendsto_zero_of_varianceOrder_eq
-- given
  (hvar : forall n, OddPrismUnequalBridgeVarianceOrder (Ising.betaC 3) n) :
-- imply
  Tendsto (standardCubicInterfaceDensity (Ising.betaC 3)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.standardCubicInterfaceDensity_critical_tendsto_zero_of_varianceOrder hvar

/--
[rectangularIsingSurfaceTension_critical_eq_zero_of_unequalVarianceOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_critical_eq_zero_of_unequalVarianceOrder_eq
-- given
  (hprism : HasPrismCubicalSurfaceComparison (Ising.betaC 3))
  (hvar : forall n, OddPrismUnequalBridgeVarianceOrder (Ising.betaC 3) n) :
-- imply
  rectangularIsingSurfaceTension (Ising.betaC 3) = 0 := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_critical_eq_zero_of_unequalVarianceOrder hprism hvar


-- created on 2026-10-23
