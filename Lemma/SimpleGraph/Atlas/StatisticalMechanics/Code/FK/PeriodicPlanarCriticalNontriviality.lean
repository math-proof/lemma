import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalNontriviality.Part8
open MeasureTheory Set SimpleGraph Filter Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.degree_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma degree_shift_eq
  {V : Type u}
  [DecidableEq V]
  {P : PeriodicGraph V}
  {z : Lattice.Site 2}
  {v : V} :
-- imply
  P.vertexDegree (P.shift z v) = P.vertexDegree v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.degree_shift P z v

/--
[PeriodicGraph.degree_le_degreeBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma degree_le_degreeBound_eq
  {V : Type u}
  [DecidableEq V]
  {P : PeriodicGraph V}
  {v : V} :
-- imply
  P.vertexDegree v ≤ P.degreeBound := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.degree_le_degreeBound P v

/--
[RootedWalkCode.length_toWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma length_toWalk_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  [SimpleGraph.LocallyFinite G]
  {u : V}
  {n : Nat}
  {c : RootedWalkCode G u n} :
-- imply
  (c.toWalk G).2.length = n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.RootedWalkCode.length_toWalk G c

/--
[RootedWalkCode.toWalk_ofWalk_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma toWalk_ofWalk_endpoint_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  [SimpleGraph.LocallyFinite G]
  {u v : V}
  {p : G.Walk u v} :
-- imply
  ((RootedWalkCode.ofWalk G p).toWalk G).1 = v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.RootedWalkCode.toWalk_ofWalk_endpoint G p

/--
[RootedWalkCode.toWalk_ofWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma toWalk_ofWalk_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  [SimpleGraph.LocallyFinite G]
  {u v : V}
  {p : G.Walk u v} :
-- imply
  (RootedWalkCode.ofWalk G p).toWalk G = ⟨v, p⟩ := by
-- proof
  apply StatMech.FK.PeriodicPlanar.RootedWalkCode.toWalk_ofWalk G p

/--
[RootedWalkCode.toWalk_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma toWalk_cast_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  [SimpleGraph.LocallyFinite G]
  {u : V}
  {m n : Nat}
  {c : RootedWalkCode G u m}
-- given
  (h : m = n) :
-- imply
  (h ▸ c).toWalk G = c.toWalk G := by
-- proof
  apply StatMech.FK.PeriodicPlanar.RootedWalkCode.toWalk_cast G h c

/--
[card_rootedWalkCode_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma card_rootedWalkCode_le_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  [SimpleGraph.LocallyFinite G]
  {D : Nat}
  {u : V}
  {n : Nat}
-- given
  (hD : ∀ v, G.degree v ≤ D) :
-- imply
  Fintype.card (RootedWalkCode G u n) ≤ D ^ n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.card_rootedWalkCode_le G hD u n

/--
[endpoint_mem_rootedReachableFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma endpoint_mem_rootedReachableFinset_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  [SimpleGraph.LocallyFinite G]
  {u v : V}
  {p : G.Walk u v}
  {n : Nat}
-- given
  (hp : p.length < n) :
-- imply
  v ∈ rootedReachableFinset G u n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.endpoint_mem_rootedReachableFinset G p hp

/--
[isClopen_walkOpenEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma isClopen_walkOpenEvent_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v} :
-- imply
  IsClopen (walkOpenEvent p) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.isClopen_walkOpenEvent p

/--
[isIncreasing_walkOpenEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma isIncreasing_walkOpenEvent_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v} :
-- imply
  IsIncreasing (walkOpenEvent p) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.isIncreasing_walkOpenEvent p

/--
[isClopen_rootedOpenPathEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma isClopen_rootedOpenPathEvent_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  [SimpleGraph.LocallyFinite G]
  {u : V}
  {n : Nat} :
-- imply
  IsClopen (rootedOpenPathEvent G u n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.isClopen_rootedOpenPathEvent G u n

/--
[isIncreasing_rootedOpenPathEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma isIncreasing_rootedOpenPathEvent_eq
  {V : Type u}
  [DecidableEq V]
  {G : SimpleGraph V}
  [SimpleGraph.LocallyFinite G]
  {u : V}
  {n : Nat} :
-- imply
  IsIncreasing (rootedOpenPathEvent G u n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.isIncreasing_rootedOpenPathEvent G u n

/--
[PeriodicGraph.openSubgraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma openSubgraph_le_eq
  {V : Type u}
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  P.openSubgraph omega ≤ P.graph := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.openSubgraph_le P omega

/--
[PeriodicGraph.open_of_mem_walk_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma open_of_mem_walk_edges_eq
  {V : Type u}
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {u v : V}
  {p : (P.openSubgraph omega).Walk u v}
  {e : Sym2 V}
-- given
  (he : e ∈ p.edges) :
-- imply
  omega e = true := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.open_of_mem_walk_edges P omega p he

/--
[PeriodicGraph.percolationEvent_subset_rootedOpenPathEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma percolationEvent_subset_rootedOpenPathEvent_eq
  {V : Type u}
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : Nat} :
-- imply
  P.percolationEvent ⊆ P.rootedOpenPathEvent n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.percolationEvent_subset_rootedOpenPathEvent P n

/--
[PeriodicGraph.wiredBufferedMeasure_real_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma wiredBufferedMeasure_real_eq_eq
  {V : Type u}
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {m : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hA : MeasurableSet A) :
-- imply
  (P.wiredBufferedMeasure m hp hp1 hq : Measure (ConfigSpace (Sym2 V))).real A = ∑ omega : ConfigSpace (Sym2 (P.BufferedVertex m)), (P.extendEdge (P.bufferedRadius m) ⁻¹' A).indicator (fun _ => (1 : Real)) omega * wiredFkProb (P.bufferedGraph m) (P.bufferedBoundary m) p q omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedMeasure_real_eq P m hp hp1 hq A hA

/--
[PeriodicGraph.range_of_extendEdge_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma range_of_extendEdge_true_eq
  {V : Type u}
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {r : Nat}
  {omega : ConfigSpace (Sym2 (P.OrbitVertex r))}
  {e : Sym2 V}
-- given
  (h : P.extendEdge r omega e = true) :
-- imply
  e ∈ Set.range (P.edgeIncl r) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.range_of_extendEdge_true P r omega e h

/--
[PeriodicGraph.orbitEdge_mem_of_edgeIncl_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma orbitEdge_mem_of_edgeIncl_mem_eq
  {V : Type u}
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {r : Nat}
  {be : Sym2 (P.OrbitVertex r)}
-- given
  (he : P.edgeIncl r be ∈ P.graph.edgeSet) :
-- imply
  be ∈ (P.orbitGraph r).edgeFinset := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.orbitEdge_mem_of_edgeIncl_mem P r be he

/--
[PeriodicGraph.exists_bufferedPathEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma exists_bufferedPathEdges_eq
  {V : Type u}
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {m : Nat}
  {u v : V}
  {p : P.graph.Walk u v}
-- given
  (hp : p.IsPath)
  (hrange : ∀ e ∈ p.edges, e ∈ Set.range (P.edgeIncl (P.bufferedRadius m))) :
-- imply
  ∃ F : Finset (Sym2 (P.BufferedVertex m)), F ⊆ (P.bufferedGraph m).edgeFinset ∧ F.card = p.length ∧ (P.extendEdge (P.bufferedRadius m) ⁻¹' walkOpenEvent p ⊆ {omega | ∀ be ∈ F, omega be = true}) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.exists_bufferedPathEdges P m p hp hrange

/--
[PeriodicGraph.bernoulli_buffered_walkOpenEvent_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma bernoulli_buffered_walkOpenEvent_le_eq
  {V : Type u}
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {m : Nat}
  {u v : V}
  {path : P.graph.Walk u v}
  {p : Real}
-- given
  (hpath : path.IsPath)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ∑ omega : ConfigSpace (Sym2 (P.BufferedVertex m)), (P.extendEdge (P.bufferedRadius m) ⁻¹' walkOpenEvent path).indicator (fun _ => (1 : Real)) omega * fkProb (P.bufferedGraph m) p 1 omega ≤ p ^ path.length := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bernoulli_buffered_walkOpenEvent_le P m path hpath hp hp1

/--
[PeriodicGraph.wiredBufferedMeasure_rootedOpenPathEvent_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma wiredBufferedMeasure_rootedOpenPathEvent_le_eq
  {V : Type u}
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {m n : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real (P.rootedOpenPathEvent n) ≤ ((P.degreeBound : Real) * p) ^ n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedMeasure_rootedOpenPathEvent_le P m n hp hp1 hq

/--
[PeriodicGraph.isClopen_rootedOpenPathEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma isClopen_rootedOpenPathEvent_eq_2
  {V : Type u}
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {n : Nat} :
-- imply
  IsClopen (P.rootedOpenPathEvent n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.isClopen_rootedOpenPathEvent P n

/--
[PeriodicGraph.wiredPercolationProbability_le_pow_degreeBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma wiredPercolationProbability_le_pow_degreeBound_eq
  {V : Type u}
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : Real}
  {n : Nat}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  P.wiredPercolationProbability p q ≤ ((P.degreeBound : Real) * p) ^ n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredPercolationProbability_le_pow_degreeBound P hp hp1 hq n

/--
[PeriodicGraph.wiredPercolationProbability_eq_zero_of_degreeBound_mul_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma wiredPercolationProbability_eq_zero_of_degreeBound_mul_lt_one_eq
  {V : Type u}
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hsmall : (P.degreeBound : Real) * p < 1) :
-- imply
  P.wiredPercolationProbability p q = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredPercolationProbability_eq_zero_of_degreeBound_mul_lt_one P hp hp1 hq hsmall

/--
[PeriodicGraph.criticalPoint_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma criticalPoint_pos_eq
  {V : Type u}
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {q : Real}
-- given
  (hq : 1 ≤ q) :
-- imply
  0 < P.criticalPoint q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.criticalPoint_pos P hq

/--
[PeriodicGraph.criticalPoints_mem_Ioo_of_bidirectionalCoverage_qge_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma criticalPoints_mem_Ioo_of_bidirectionalCoverage_qge_one_eq
  {V : Type u}
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {P : PeriodicGraph V}
  {Pdual : PeriodicGraph W}
  {q : Real}
-- given
  (hq : 1 ≤ q)
  (hcoverage : DualSubcriticalCoverage (fun r => Pdual.wiredPercolates r q) (P.criticalPoint q) q)
  (hcoverageDual : DualSubcriticalCoverage (fun r => P.wiredPercolates r q) (Pdual.criticalPoint q) q) :
-- imply
  P.criticalPoint q ∈ Ioo (0 : Real) 1 ∧ Pdual.criticalPoint q ∈ Ioo (0 : Real) 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.criticalPoints_mem_Ioo_of_bidirectionalCoverage_qge_one P Pdual hq hcoverage hcoverageDual

/--
[PeriodicGraph.dualCritical_relation_of_bidirectionalCoverage_noCoexistence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean)
-/
@[path]
private lemma dualCritical_relation_of_bidirectionalCoverage_noCoexistence_eq
  {V : Type u}
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {P : PeriodicGraph V}
  {Pdual : PeriodicGraph W}
  {q : Real}
-- given
  (hq : 1 ≤ q)
  (hcoverage : DualSubcriticalCoverage (fun r => Pdual.wiredPercolates r q) (P.criticalPoint q) q)
  (hcoverageDual : DualSubcriticalCoverage (fun r => P.wiredPercolates r q) (Pdual.criticalPoint q) q)
  (hnoCoexistence : DualNoCoexistence (fun r => P.wiredPercolates r q) (fun r => Pdual.wiredPercolates r q) q) :
-- imply
  BeffaraDC.dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧ (P.criticalPoint q / (1 - P.criticalPoint q)) * (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.dualCritical_relation_of_bidirectionalCoverage_noCoexistence P Pdual hq hcoverage hcoverageDual hnoCoexistence


-- created on 2026-10-23
