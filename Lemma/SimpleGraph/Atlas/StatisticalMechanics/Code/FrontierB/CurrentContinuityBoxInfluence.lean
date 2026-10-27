import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityBoxInfluence
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[boxCurrentEdgeOfAdjacent_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityBoxInfluence.lean)
-/
@[path]
private lemma boxCurrentEdgeOfAdjacent_endpoints_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : ℕ}
  {x y : Site d}
-- given
  (hx : x ∈ box d n)
  (hy : y ∈ box d n)
  (hxy : (hypercubicLattice d).Adj x y) :
-- imply
  let e := boxCurrentEdgeOfAdjacent hx hy hxy ({e.1.out.1, e.1.out.2} : Finset (StatMech.FK.boxVerts d n)) = ({(⟨x, hx⟩ : StatMech.FK.boxVerts d n), (⟨y, hy⟩ : StatMech.FK.boxVerts d n)} : Finset _) := by
-- proof
  apply StatMech.FrontierB.boxCurrentEdgeOfAdjacent_endpoints G hx hy hxy

/--
[boundarySourceCurrentPairPMF_superpositionEvent_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityBoxInfluence.lean)
-/
@[path]
private lemma boundarySourceCurrentPairPMF_superpositionEvent_real_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {interior internalSources exactSecondSources : Finset V}
  [DecidablePred P]
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hfirst : 0 < boundarySourceCurrentSum G beta J interior internalSources)
  (hsecond : 0 < currentSum G beta J exactSecondSources)
  (P : Current V -> Prop) :
-- imply
  (boundarySourceCurrentPairPMF G beta J hbeta hJ interior internalSources exactSecondSources hfirst hsecond).toMeasure.real (sourcePairSuperpositionEvent G P) = boundarySourceGatedPairSum G beta J interior internalSources exactSecondSources P / (boundarySourceCurrentSum G beta J interior internalSources * currentSum G beta J exactSecondSources) := by
-- proof
  apply StatMech.FrontierB.boundarySourceCurrentPairPMF_superpositionEvent_real G beta J hbeta hJ interior internalSources exactSecondSources hfirst hsecond P

/--
[boundarySource_twoPoint_ratio_gap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityBoxInfluence.lean)
-/
@[path]
private lemma boundarySource_twoPoint_ratio_gap_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {interior : Finset V}
  {u v : V}
-- given
  (hbeta : 0 ≤ beta)
  (huv : u ≠ v)
  (hu : u ∈ interior)
  (hv : v ∈ interior) :
-- imply
  0 ≤ boundarySourceCurrentSum G beta (fun _ => 1) interior {u, v} / boundarySourceCurrentSum G beta (fun _ => 1) interior ∅ - currentSum G beta (fun _ => 1) {u, v} / currentSum G beta (fun _ => 1) ∅ := by
-- proof
  apply StatMech.FrontierB.boundarySource_twoPoint_ratio_gap_nonneg G beta hbeta interior huv hu hv

/--
[sourcePairSuperpositionEvent_exterior_eq_boundaryConnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityBoxInfluence.lean)
-/
@[path]
private lemma sourcePairSuperpositionEvent_exterior_eq_boundaryConnection_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : ℕ}
  {x : StatMech.FK.boxVerts d n} :
-- imply
  sourcePairSuperpositionEvent (StatMech.FK.boxGraph d n) (fun m => ∃ z, z ∉ boxCurrentInterior d n ∧ CurrentConnected (StatMech.FK.boxGraph d n) m x z) = (Prod.map (extendBoxCurrent d n) (extendBoxCurrent d n)) ⁻¹' (superposedCurrentTrace ⁻¹' traceBoundaryConnectionEvent n (x : Site d)) := by
-- proof
  apply StatMech.FrontierB.sourcePairSuperpositionEvent_exterior_eq_boundaryConnection G d n x

/--
[traceBoundaryConnectionEvent_subset_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityBoxInfluence.lean)
-/
@[path]
private lemma traceBoundaryConnectionEvent_subset_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d m n : ℕ}
  {x : Site d}
-- given
  (hm : 1 ≤ m)
  (hx : x ∈ box d (m - 1))
  (hmn : m ≤ n) :
-- imply
  traceBoundaryConnectionEvent n x ⊆ traceBoundaryConnectionEvent m x := by
-- proof
  apply StatMech.FrontierB.traceBoundaryConnectionEvent_subset_le G hm hx hmn

/--
[traceBoundaryConnectionEvent_subset_crossingEventFrom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityBoxInfluence.lean)
-/
@[path]
private lemma traceBoundaryConnectionEvent_subset_crossingEventFrom_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : ℕ}
  {x : Site d} :
-- imply
  traceBoundaryConnectionEvent n x ⊆ crossingEventFrom d x n := by
-- proof
  apply StatMech.FrontierB.traceBoundaryConnectionEvent_subset_crossingEventFrom G

/--
[crossingEventFrom_real_tendsto_clusterInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityBoxInfluence.lean)
-/
@[path]
private lemma crossingEventFrom_real_tendsto_clusterInfinite_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {x : Site d} :
-- imply
  Tendsto (fun n => (mu : Measure _).real (crossingEventFrom d x n)) atTop (nhds ((mu : Measure _).real (StatMech.FK.clusterInfiniteEvent d x))) := by
-- proof
  apply StatMech.FrontierB.crossingEventFrom_real_tendsto_clusterInfinite G d mu x

/--
[beta_mul_box_twoPoint_gap_le_boundaryConnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityBoxInfluence.lean)
-/
@[path]
private lemma beta_mul_box_twoPoint_gap_le_boundaryConnection_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : ℕ}
  {beta : ℝ}
  {e : (StatMech.FK.boxGraph d n).edgeFinset}
-- given
  (hbeta : 0 < beta)
  (hleft : e.1.out.1 ∈ boxCurrentInterior d n)
  (hright : e.1.out.2 ∈ boxCurrentInterior d n) :
-- imply
  beta * (boundarySourceCurrentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) (boxCurrentInterior d n) {e.1.out.1, e.1.out.2} / boundarySourceCurrentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) (boxCurrentInterior d n) ∅ - currentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) {e.1.out.1, e.1.out.2} / currentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) ∅) ≤ ((plusBoxCurrentMeasure d n beta hbeta.le).prod (freeBoxCurrentMeasure d n beta hbeta.le) : Measure _).real (superposedCurrentTrace ⁻¹' traceBoundaryConnectionEvent n (e.1.out.1 : Site d)) := by
-- proof
  apply StatMech.FrontierB.beta_mul_box_twoPoint_gap_le_boundaryConnection G d n beta hbeta e hleft hright

/--
[beta_mul_box_pair_gap_le_boundaryConnection_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityBoxInfluence.lean)
-/
@[path]
private lemma beta_mul_box_pair_gap_le_boundaryConnection_union_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d n)
  (hy : y ∈ box d n)
  (hxy : (hypercubicLattice d).Adj x y)
  (hxint : (⟨x, hx⟩ : StatMech.FK.boxVerts d n) ∈ boxCurrentInterior d n)
  (hyint : (⟨y, hy⟩ : StatMech.FK.boxVerts d n) ∈ boxCurrentInterior d n) :
-- imply
  beta * (boundarySourceCurrentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) (boxCurrentInterior d n) {(⟨x, hx⟩ : StatMech.FK.boxVerts d n), ⟨y, hy⟩} / boundarySourceCurrentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) (boxCurrentInterior d n) ∅ - currentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) {(⟨x, hx⟩ : StatMech.FK.boxVerts d n), ⟨y, hy⟩} / currentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) ∅) ≤ ((plusBoxCurrentMeasure d n beta hbeta.le).prod (freeBoxCurrentMeasure d n beta hbeta.le) : Measure _).real (superposedCurrentTrace ⁻¹' (traceBoundaryConnectionEvent n x ∪ traceBoundaryConnectionEvent n y)) := by
-- proof
  apply StatMech.FrontierB.beta_mul_box_pair_gap_le_boundaryConnection_union G d n beta hbeta x y hx hy hxy hxint hyint


-- created on 2026-10-23
