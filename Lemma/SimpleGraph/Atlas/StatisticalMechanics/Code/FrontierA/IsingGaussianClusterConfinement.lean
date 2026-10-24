import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingGaussianClusterConfinement
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[mem_finiteTreeSafeRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianClusterConfinement.lean)
-/
@[path]
private lemma mem_finiteTreeSafeRegion_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {roots : Finset V}
  {v : V} :
-- imply
  v ∈ finiteTreeSafeRegion G m roots ↔ ∀ g ∈ roots, ¬ CurrentConnected G m g v := by
-- proof
  apply StatMech.FrontierA.mem_finiteTreeSafeRegion G m roots v

/--
[finiteTreeSafeRegion_subset_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianClusterConfinement.lean)
-/
@[path]
private lemma finiteTreeSafeRegion_subset_compl_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {roots : Finset V} :
-- imply
  finiteTreeSafeRegion G m roots ⊆ rootsᶜ := by
-- proof
  apply StatMech.FrontierA.finiteTreeSafeRegion_subset_compl G m roots

/--
[finiteTreeSafeRegion_closed_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianClusterConfinement.lean)
-/
@[path]
private lemma finiteTreeSafeRegion_closed_of_connected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {roots : Finset V}
  {u v : V}
-- given
  (hu : u ∈ finiteTreeSafeRegion G m roots)
  (huv : CurrentConnected G m u v) :
-- imply
  v ∈ finiteTreeSafeRegion G m roots := by
-- proof
  apply StatMech.FrontierA.finiteTreeSafeRegion_closed_of_connected G m roots hu huv

/--
[finiteTreeSafeRegion_noCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianClusterConfinement.lean)
-/
@[path]
private lemma finiteTreeSafeRegion_noCrossing_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {roots T : Finset V}
-- given
  (hev : finiteTreeSafeRegion G m roots = T) :
-- imply
  NoCrossing G m T := by
-- proof
  apply StatMech.FrontierA.finiteTreeSafeRegion_noCrossing G m roots T hev

/--
[finiteTreeSafeRegion_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianClusterConfinement.lean)
-/
@[path]
private lemma finiteTreeSafeRegion_congr_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m m' : Current V}
  {roots T : Finset V}
-- given
  (hev : finiteTreeSafeRegion G m roots = T)
  (hagree : ∀ e ∈ G.edgeFinset, ¬ edgeInside T e -> m e = m' e) :
-- imply
  finiteTreeSafeRegion G m' roots = T := by
-- proof
  apply StatMech.FrontierA.finiteTreeSafeRegion_congr G m m' roots T hev hagree

/--
[finiteTreeSafeRegionFiber_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianClusterConfinement.lean)
-/
@[path]
private lemma finiteTreeSafeRegionFiber_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {roots T : Finset V}
  {A C : Finset V}
-- given
  (J : Sym2 V -> Real)
  (hA : A ⊆ T)
  (hC : C ⊆ T) :
-- imply
  finiteTreeSafeRegionFiber G beta J roots T A C = currentSum G beta (couplingIn J T) A * currentSum G beta (couplingIn J T) C * finiteTreeSafeRegionContext G beta J roots T := by
-- proof
  apply StatMech.FrontierA.finiteTreeSafeRegionFiber_factor G beta J roots T A C hA hC

/--
[finiteTreeSafeRegionFiber_sourceReplacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianClusterConfinement.lean)
-/
@[path]
private lemma finiteTreeSafeRegionFiber_sourceReplacement_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {roots T : Finset V}
  {A : Finset V}
-- given
  (J : Sym2 V -> Real)
  (hA : A ⊆ T) :
-- imply
  finiteTreeSafeRegionFiber G beta J roots T A ∅ = expectationJ G beta (couplingIn J T) A * finiteTreeSafeRegionFiber G beta J roots T ∅ ∅ := by
-- proof
  apply StatMech.FrontierA.finiteTreeSafeRegionFiber_sourceReplacement G beta J roots T A hA

/--
[finiteTreeSafeRegionFiber_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianClusterConfinement.lean)
-/
@[path]
private lemma finiteTreeSafeRegionFiber_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {roots T A C : Finset V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e) :
-- imply
  0 <= finiteTreeSafeRegionFiber G beta J roots T A C := by
-- proof
  apply StatMech.FrontierA.finiteTreeSafeRegionFiber_nonneg G beta J hbeta hJ roots T A C

/--
[finiteTreeClusterConfinementMass_eq_fibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianClusterConfinement.lean)
-/
@[path]
private lemma finiteTreeClusterConfinementMass_eq_fibers_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {k l : V}
  {S : Finset V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  finiteTreeClusterConfinementMass G beta J k l S = ∑ T : Finset V, if k ∈ T then finiteTreeSafeRegionFiber G beta J Sᶜ T {k, l} ∅ else 0 := by
-- proof
  apply StatMech.FrontierA.finiteTreeClusterConfinementMass_eq_fibers G beta J k l S

/--
[sum_finiteTreeSafeRegionFiber_vacuum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianClusterConfinement.lean)
-/
@[path]
private lemma sum_finiteTreeSafeRegionFiber_vacuum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {roots : Finset V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  ∑ T : Finset V, finiteTreeSafeRegionFiber G beta J roots T ∅ ∅ = currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.sum_finiteTreeSafeRegionFiber_vacuum G beta J roots

/--
[finiteTreeClusterConfinementMass_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianClusterConfinement.lean)
-/
@[path]
private lemma finiteTreeClusterConfinementMass_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {k l : V}
  {S : Finset V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hkl : k ≠ l) :
-- imply
  finiteTreeClusterConfinementMass G beta J k l S <= expectationJ G beta (couplingIn J S) {k, l} * currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.finiteTreeClusterConfinementMass_le G beta J hbeta hJ hkl S


-- created on 2026-10-23
