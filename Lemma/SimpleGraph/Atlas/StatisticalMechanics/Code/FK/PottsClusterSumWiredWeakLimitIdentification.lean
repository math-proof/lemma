import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredWeakLimitIdentification.Part9
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.Wired


/--
[measurable_extendWiredEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma measurable_extendWiredEdge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat} :
-- imply
  Measurable (extendWiredEdge d n) := by
-- proof
  apply StatMech.FK.measurable_extendWiredEdge G d n

/--
[extendWiredEdge_eq_of_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma extendWiredEdge_eq_of_range_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat}
  {n : Nat}
  {be : Sym2 (boxVerts d n)}
  {omega : ConfigSpace (Sym2 (boxVerts d n))} :
-- imply
  extendWiredEdge d n omega (edgeIncl d n be) = omega be := by
-- proof
  apply StatMech.FK.extendWiredEdge_eq_of_range G n be omega

/--
[extendWiredEdge_eq_true_of_not_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma extendWiredEdge_eq_true_of_not_range_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat}
  {n : Nat}
  {omega : ConfigSpace (Sym2 (boxVerts d n))}
  {e : Sym2 (Site d)}
-- given
  (he : e ∉ Set.range (edgeIncl d n)) :
-- imply
  extendWiredEdge d n omega e = true := by
-- proof
  apply StatMech.FK.extendWiredEdge_eq_true_of_not_range G n omega he

/--
[boxRestrict_extendWiredEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma boxRestrict_extendWiredEdge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat}
  {omega : ConfigSpace (Sym2 (boxVerts d n))} :
-- imply
  boxRestrict d n (extendWiredEdge d n omega) = omega := by
-- proof
  apply StatMech.FK.boxRestrict_extendWiredEdge G d n omega

/--
[extendWiredEdge_restrict_eq_extendEdge_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma extendWiredEdge_restrict_eq_extendEdge_restrict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat}
  {n : Nat}
  {omega : ConfigSpace (Sym2 (boxVerts d n))}
  {edges : Finset (Sym2 (Site d))}
-- given
  (hedges : ∀ e ∈ edges, e ∈ Set.range (edgeIncl d n)) :
-- imply
  edges.restrict (extendWiredEdge d n omega) = edges.restrict (extendEdge d n omega) := by
-- proof
  apply StatMech.FK.extendWiredEdge_restrict_eq_extendEdge_restrict G n omega edges hedges

/--
[eventually_wiredOpenExteriorFiniteMeasure_eq_wiredFiniteMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma eventually_wiredOpenExteriorFiniteMeasure_eq_wiredFiniteMeasure_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (phi : Nat -> Nat)
  (hphi : StrictMono phi)
  (hA : IsClopen A) :
-- imply
  Filter.EventuallyEq atTop (fun k => ((wiredOpenExteriorFiniteMeasure d (phi k) hp hp1 hq : ProbabilityMeasure _) : Measure _) A) (fun k => ((wiredFiniteMeasure d (phi k) hp hp1 hq : ProbabilityMeasure _) : Measure _) A) := by
-- proof
  apply StatMech.FK.eventually_wiredOpenExteriorFiniteMeasure_eq_wiredFiniteMeasure G hp hp1 hq phi hphi A hA

/--
[tendsto_wiredOpenExteriorFiniteMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma tendsto_wiredOpenExteriorFiniteMeasure_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat}
  {p q : Real}
  {edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (phi : Nat -> Nat)
  (hphi : StrictMono phi)
  (hclosed : Tendsto (fun k => wiredFiniteMeasure d (phi k) hp hp1 hq) atTop (nhds edgeLimit)) :
-- imply
  Tendsto (fun k => wiredOpenExteriorFiniteMeasure d (phi k) hp hp1 hq) atTop (nhds edgeLimit) := by
-- proof
  apply StatMech.FK.tendsto_wiredOpenExteriorFiniteMeasure G hp hp1 hq phi hphi edgeLimit hclosed

/--
[connected_extendWiredEdge_of_boxConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma connected_extendWiredEdge_of_boxConnected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat}
  {omega : ConfigSpace (Sym2 (boxVerts d n))}
  {x y : boxVerts d n}
-- given
  (hxy : (openSub (boxGraph d n) omega).Reachable x y) :
-- imply
  Lattice.Connected d (extendWiredEdge d n omega) (x : Site d) (y : Site d) := by
-- proof
  apply StatMech.FK.connected_extendWiredEdge_of_boxConnected G omega hxy

/--
[cluster_extendWiredEdge_infinite_of_connToBdry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma cluster_extendWiredEdge_infinite_of_connToBdry_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat}
  {omega : ConfigSpace (Sym2 (boxVerts d n))}
  {x : boxVerts d n}
-- given
  (hd : 2 ≤ d)
  (hn : 1 ≤ n)
  (hconn : IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega x) :
-- imply
  (cluster d (extendWiredEdge d n omega) (x : Site d)).Infinite := by
-- proof
  apply StatMech.FK.cluster_extendWiredEdge_infinite_of_connToBdry G hd hn omega x hconn

/--
[connToBdry_of_extendWired_connected_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma connToBdry_of_extendWired_connected_outside_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat}
  {omega : ConfigSpace (Sym2 (boxVerts d n))}
  {x : boxVerts d n}
  {v : Site d}
-- given
  (hn : 1 ≤ n)
  (hv : v ∉ box d n)
  (hreach : (openSubgraph d (extendWiredEdge d n omega)).Reachable (x : Site d) v) :
-- imply
  IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega x := by
-- proof
  apply StatMech.FK.connToBdry_of_extendWired_connected_outside G hn omega x hv hreach

/--
[connToBdry_or_boxConnected_of_extendWired_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma connToBdry_or_boxConnected_of_extendWired_connected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat}
  {omega : ConfigSpace (Sym2 (boxVerts d n))}
  {x y : boxVerts d n}
-- given
  (hn : 1 ≤ n)
  (hreach : (openSubgraph d (extendWiredEdge d n omega)).Reachable (x : Site d) (y : Site d)) :
-- imply
  IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega x ∨ (openSub (boxGraph d n) omega).Reachable x y := by
-- proof
  apply StatMech.FK.connToBdry_or_boxConnected_of_extendWired_connected G hn omega x y hreach

/--
[cluster_extendWiredEdge_finite_of_not_connToBdry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma cluster_extendWiredEdge_finite_of_not_connToBdry_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat}
  {omega : ConfigSpace (Sym2 (boxVerts d n))}
  {x : boxVerts d n}
-- given
  (hn : 1 ≤ n)
  (hconn : ¬ IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega x) :
-- imply
  (cluster d (extendWiredEdge d n omega) (x : Site d)).Finite := by
-- proof
  apply StatMech.FK.cluster_extendWiredEdge_finite_of_not_connToBdry G hn omega x hconn

/--
[cluster_extendWiredEdge_infinite_iff_connToBdry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma cluster_extendWiredEdge_infinite_iff_connToBdry_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat}
  {omega : ConfigSpace (Sym2 (boxVerts d n))}
  {x : boxVerts d n}
-- given
  (hd : 2 ≤ d)
  (hn : 1 ≤ n) :
-- imply
  (cluster d (extendWiredEdge d n omega) (x : Site d)).Infinite ↔ IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega x := by
-- proof
  apply StatMech.FK.cluster_extendWiredEdge_infinite_iff_connToBdry G hd hn omega x

/--
[wiredSub_reachable_connected_extendWiredEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma wiredSub_reachable_connected_extendWiredEdge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat}
  {omega : ConfigSpace (Sym2 (boxVerts d n))}
  {x y : boxVerts d n}
-- given
  (hd : 2 ≤ d)
  (hn : 1 ≤ n)
  (hxy : (IsingFK.wiredSub (boxGraph d n) (boxBoundary d n) omega).Reachable x y) :
-- imply
  Lattice.Connected d (extendWiredEdge d n omega) (x : Site d) (y : Site d) := by
-- proof
  apply StatMech.FK.wiredSub_reachable_connected_extendWiredEdge G hd hn omega hxy

/--
[extendWiredNonboundaryRepresentatives_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma extendWiredNonboundaryRepresentatives_law_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {omega : ConfigSpace (Sym2 (boxVerts d n))}
  {v0 : boxVerts d n}
-- given
  (hd : 2 ≤ d)
  (hn : 1 ≤ n)
  (hv0 : boxBoundary d n v0) :
-- imply
  let W := IsingFK.wiredSub (boxGraph d n) (boxBoundary d n) omega let c0 := W.connectedComponentMk v0 let K := {C : W.ConnectedComponent // C ≠ c0} let r : K -> Site d := fun C => (C.1.out : boxVerts d n) Measure.map (fun label C => pottsClusterSumSpin boundaryColor (extendWiredEdge d n omega) label (r C)) (pottsIIDLabelMeasure d q) = Measure.infinitePi fun _ : K => (PMF.uniformOfFintype (Fin q)).toMeasure := by
-- proof
  apply StatMech.FK.extendWiredNonboundaryRepresentatives_law G hd hn boundaryColor omega v0 hv0

/--
[nonboundaryWiredComponentColorsEquivCompatibleBoundarySpin_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma nonboundaryWiredComponentColorsEquivCompatibleBoundarySpin_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : Nat}
  {b : Fin q}
  {omega : ConfigSpace (Sym2 V)}
  {v0 : V}
  {x : V}
-- given
  (bdry : V -> Prop)
  (hv0 : bdry v0)
  (color : {C : (wiredSub G bdry omega).ConnectedComponent // C ≠ (wiredSub G bdry omega).connectedComponentMk v0} -> Fin q) :
-- imply
  (nonboundaryWiredComponentColorsEquivCompatibleBoundarySpin G bdry b omega v0 hv0 color).1 x = if h : (wiredSub G bdry omega).connectedComponentMk x = (wiredSub G bdry omega).connectedComponentMk v0 then b else color ⟨(wiredSub G bdry omega).connectedComponentMk x, h⟩ := by
-- proof
  apply StatMech.FK.Wired.nonboundaryWiredComponentColorsEquivCompatibleBoundarySpin_apply G bdry b omega v0 hv0 color x

/--
[conditionalClusterColorPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma conditionalClusterColorPMF_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : Nat}
  [NeZero q]
  {b : Fin q}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (bdry : V -> Prop)
  (sigma : V -> Fin q) :
-- imply
  conditionalClusterColorPMF G bdry b omega sigma = if h : ConstOnOpen G omega sigma ∧ BoundaryFixed bdry b sigma then (Fintype.card (CompatibleBoundarySpin G bdry b omega) : ENNReal)⁻¹ else 0 := by
-- proof
  apply StatMech.FK.Wired.conditionalClusterColorPMF_apply G bdry b omega sigma

/--
[conditionalClusterColorPMF_eq_pinnedWiredComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma conditionalClusterColorPMF_eq_pinnedWiredComponents_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : Nat}
  [NeZero q]
  {b : Fin q}
  {omega : ConfigSpace (Sym2 V)}
  {v0 : V}
-- given
  (bdry : V -> Prop)
  (hv0 : bdry v0) :
-- imply
  conditionalClusterColorPMF G bdry b omega = (PMF.uniformOfFintype {tau : (wiredSub G bdry omega).ConnectedComponent -> Fin q // tau ((wiredSub G bdry omega).connectedComponentMk v0) = b}).map (fun tau x => tau.1 ((wiredSub G bdry omega).connectedComponentMk x)) := by
-- proof
  apply StatMech.FK.Wired.conditionalClusterColorPMF_eq_pinnedWiredComponents G bdry b omega v0 hv0

/--
[extendWiredClusterSumSpin_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma extendWiredClusterSumSpin_law_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d n q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {omega : ConfigSpace (Sym2 (boxVerts d n))}
  {v0 : boxVerts d n}
-- given
  (bdry : V -> Prop)
  (hd : 2 ≤ d)
  (hn : 1 ≤ n)
  (hv0 : boxBoundary d n v0) :
-- imply
  Measure.map (fun label (x : boxVerts d n) => pottsClusterSumSpin boundaryColor (extendWiredEdge d n omega) label (x : Site d)) (pottsIIDLabelMeasure d q) = (conditionalClusterColorPMF (boxGraph d n) (boxBoundary d n) boundaryColor omega).toMeasure := by
-- proof
  apply StatMech.FK.Wired.extendWiredClusterSumSpin_law G bdry hd hn boundaryColor omega v0 hv0

/--
[ivp_wiredJointProb_eq_wiredFkProb_div_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma ivp_wiredJointProb_eq_wiredFkProb_div_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : Nat}
  [NeZero q]
  {b : Fin q}
  {beta J : Real}
  {v0 : V}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (bdry : V -> Prop)
  (hp : 0 < 1 - Real.exp (-(beta * J)))
  (hp1 : 1 - Real.exp (-(beta * J)) < 1)
  (hv0 : bdry v0)
  (sigma : V -> Fin q) :
-- imply
  ivp_wiredJointProb G bdry b beta J (sigma, omega) = if ConstOnOpen G omega sigma ∧ BoundaryFixed bdry b sigma then wiredFkProb G bdry (1 - Real.exp (-(beta * J))) (q : Real) omega / Fintype.card (CompatibleBoundarySpin G bdry b omega) else 0 := by
-- proof
  apply StatMech.FK.Wired.ivp_wiredJointProb_eq_wiredFkProb_div_card G bdry b beta J hp hp1 v0 hv0 sigma omega

/--
[clusterColorJointPMF_eq_ivp_wiredJointPMF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma clusterColorJointPMF_eq_ivp_wiredJointPMF_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : Nat}
  [NeZero q]
  {b : Fin q}
  {beta J : Real}
  {v0 : V}
-- given
  (bdry : V -> Prop)
  (hp : 0 < 1 - Real.exp (-(beta * J)))
  (hp1 : 1 - Real.exp (-(beta * J)) < 1)
  (hv0 : bdry v0) :
-- imply
  clusterColorJointPMF G bdry b beta J hp hp1 = ivp_wiredJointPMF G bdry b beta J hp.le := by
-- proof
  apply StatMech.FK.Wired.clusterColorJointPMF_eq_ivp_wiredJointPMF G bdry b beta J hp hp1 v0 hv0

/--
[wiredPottsJointFiniteMeasure_map_boxRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma wiredPottsJointFiniteMeasure_map_boxRestrict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d n q : Nat}
  [NeZero q]
  {b : Fin q}
  {beta J : Real}
-- given
  (bdry : V -> Prop)
  (hp : 0 ≤ 1 - Real.exp (-(beta * J))) :
-- imply
  (wiredPottsJointFiniteMeasure d n q b beta J hp).map (measurable_pottsBoxJointRestrict d n q).aemeasurable = ⟨(ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n) b beta J hp).toMeasure, inferInstance⟩ := by
-- proof
  apply StatMech.FK.Wired.wiredPottsJointFiniteMeasure_map_boxRestrict G bdry d n q b beta J hp

/--
[clusterColorJointFiniteMeasure_eq_wiredPottsJointFiniteMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean)
-/
@[path]
private lemma clusterColorJointFiniteMeasure_eq_wiredPottsJointFiniteMeasure_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {d n q : Nat}
  [NeZero q]
  {b : Fin q}
  {beta J : Real}
-- given
  (bdry : V -> Prop)
  (hd : 1 ≤ d)
  (hn : 1 ≤ n)
  (hp : 0 < 1 - Real.exp (-(beta * J)))
  (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
-- imply
  clusterColorJointFiniteMeasure d n q b beta J hp hp1 = wiredPottsJointFiniteMeasure d n q b beta J hp.le := by
-- proof
  apply StatMech.FK.Wired.clusterColorJointFiniteMeasure_eq_wiredPottsJointFiniteMeasure G bdry d n q hd hn b beta J hp hp1


-- created on 2026-10-23
