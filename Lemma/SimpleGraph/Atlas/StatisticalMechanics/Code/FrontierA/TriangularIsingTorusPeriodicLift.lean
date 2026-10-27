import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPeriodicLift.Part3
open StatMech StatMech.FrontierA


/--
[triangularIntReduce_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularIntReduce_zero_eq
  {L : Nat} :
-- imply
  triangularIntReduce L 0 = 0 := by
-- proof
  apply StatMech.FrontierA.triangularIntReduce_zero L

/--
[triangularIntReduce_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularIntReduce_add_eq
  {L : Nat}
  {p q : Int × Int} :
-- imply
  triangularIntReduce L (p + q) = triangularIntReduce L p + triangularIntReduce L q := by
-- proof
  apply StatMech.FrontierA.triangularIntReduce_add L p q

/--
[triangularIntReduce_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularIntReduce_sum_eq
  {L : Nat}
  {s : Finset alpha}
-- given
  (f : alpha -> Int × Int) :
-- imply
  triangularIntReduce L (∑ i ∈ s, f i) = ∑ i ∈ s, triangularIntReduce L (f i) := by
-- proof
  apply StatMech.FrontierA.triangularIntReduce_sum L s f

/--
[triangularIntReduce_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularIntReduce_step_eq
  {L : Nat}
  {a : Fin 6} :
-- imply
  triangularIntReduce L (triangularIntStep a) = -triangularTorusDirectionStep L a := by
-- proof
  apply StatMech.FrontierA.triangularIntReduce_step L a

/--
[triangularTorusCycleNativeDart_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularTorusCycleNativeDart_equiv_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
  {k : Fin p.darts.length} :
-- imply
  triangularTorusDartEquiv L (triangularTorusCycleNativeDart L p k) = kwGraphCycleDartLoop p k := by
-- proof
  apply StatMech.FrontierA.triangularTorusCycleNativeDart_equiv L p k

/--
[triangularTorusCycleNativeDart_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularTorusCycleNativeDart_fst_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
  {k : Fin p.darts.length} :
-- imply
  (triangularTorusCycleNativeDart L p k).1 = (kwGraphCycleDartLoop p k).fst := by
-- proof
  apply StatMech.FrontierA.triangularTorusCycleNativeDart_fst L p k

/--
[triangularTorusCycleNativeDart_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularTorusCycleNativeDart_snd_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
  {k : Fin p.darts.length} :
-- imply
  (triangularTorusCycleNativeDart L p k).2 = triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k) := by
-- proof
  apply StatMech.FrontierA.triangularTorusCycleNativeDart_snd L p k

/--
[triangularTorusCycleNativeSite_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularTorusCycleNativeSite_succ_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ forall k, (triangularTorusCycleNativeDart L p (k + 1)).1 = (triangularTorusCycleNativeDart L p k).1 + triangularIntReduce L (triangularIntStep (triangularTorusCycleNativeDart L p k).2) := by
-- proof
  apply StatMech.FrontierA.triangularTorusCycleNativeSite_succ L p hp

/--
[triangularIntPos_succ_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularIntPos_succ_cast_eq
  {m : Nat}
  {i : Fin m}
-- given
  (direction : Fin (m + 1) -> Fin 6) :
-- imply
  triangularIntPos direction i.succ = triangularIntPos direction i.castSucc + triangularIntStep (direction i.castSucc) := by
-- proof
  apply StatMech.FrontierA.triangularIntPos_succ_cast direction i

/--
[triangularCyclicSite_eq_reduce_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularCyclicSite_eq_reduce_pos_eq
  {n : Nat}
  [NeZero n]
  {k : Fin n}
-- given
  (site : Fin n -> ZMod L × ZMod L)
  (direction : Fin n -> Fin 6)
  (hsucc : forall k, site (k + 1) = site k + triangularIntReduce L (triangularIntStep (direction k))) :
-- imply
  site k = triangularIntReduce L (triangularIntPos direction k) + site 0 := by
-- proof
  apply StatMech.FrontierA.triangularCyclicSite_eq_reduce_pos site direction hsucc k

/--
[triangularTorusCycleNativeSite_eq_reduce_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularTorusCycleNativeSite_eq_reduce_pos_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ forall k, (triangularTorusCycleNativeDart L p k).1 = triangularIntReduce L (triangularIntPos (fun j => (triangularTorusCycleNativeDart L p j).2) k) + (triangularTorusCycleNativeDart L p 0).1 := by
-- proof
  apply StatMech.FrontierA.triangularTorusCycleNativeSite_eq_reduce_pos L p hp

/--
[triangularTorusCycle_totalStep_reduce_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularTorusCycle_totalStep_reduce_eq_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ triangularIntReduce L (∑ k, triangularIntStep (triangularTorusCycleNativeDart L p k).2) = 0 := by
-- proof
  apply StatMech.FrontierA.triangularTorusCycle_totalStep_reduce_eq_zero L p hp

/--
[exists_triangularTorusCycle_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma exists_triangularTorusCycle_winding_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ exists mx my : Int, (∑ k, triangularIntStep (triangularTorusCycleNativeDart L p k).2) = ((L : Int) * mx, (L : Int) * my) := by
-- proof
  apply StatMech.FrontierA.exists_triangularTorusCycle_winding L p hp

/--
[triangularIntStep_fst_eq_movementExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularIntStep_fst_eq_movementExponent_eq
  {a : Fin 6} :
-- imply
  (triangularIntStep a).1 = StatMech.Onsager.ons_dirExponentX (triangularTorusXMovementDirection a) := by
-- proof
  apply StatMech.FrontierA.triangularIntStep_fst_eq_movementExponent a

/--
[triangularIntStep_snd_eq_movementExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularIntStep_snd_eq_movementExponent_eq
  {a : Fin 6} :
-- imply
  (triangularIntStep a).2 = StatMech.Onsager.ons_dirExponentY (triangularTorusYMovementDirection a) := by
-- proof
  apply StatMech.FrontierA.triangularIntStep_snd_eq_movementExponent a

/--
[sum_triangularCycleStep_fst_eq_wrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma sum_triangularCycleStep_fst_eq_wrap_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ (∑ k, (triangularIntStep (triangularTorusCycleNativeDart L p k).2).1) = (L : Int) * ∑ k, StatMech.Onsager.ons_xWrapSign (triangularTorusXMovementDart L (triangularTorusCycleNativeDart L p k)) := by
-- proof
  apply StatMech.FrontierA.sum_triangularCycleStep_fst_eq_wrap L p hp

/--
[sum_triangularCycleStep_snd_eq_wrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma sum_triangularCycleStep_snd_eq_wrap_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ (∑ k, (triangularIntStep (triangularTorusCycleNativeDart L p k).2).2) = (L : Int) * ∑ k, StatMech.Onsager.ons_yWrapSign (triangularTorusYMovementDart L (triangularTorusCycleNativeDart L p k)) := by
-- proof
  apply StatMech.FrontierA.sum_triangularCycleStep_snd_eq_wrap L p hp

/--
[triangularTorusCycle_edges_toFinset_eq_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularTorusCycle_edges_toFinset_eq_image_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root} :
-- imply
  p.edges.toFinset = Finset.univ.image (fun k : Fin p.darts.length => (kwGraphCycleDartLoop p k).edge) := by
-- proof
  apply StatMech.FrontierA.triangularTorusCycle_edges_toFinset_eq_image L p

/--
[triangularTorusCycle_edge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularTorusCycle_edge_injective_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  Function.Injective (fun k : Fin p.darts.length => (kwGraphCycleDartLoop p k).edge) := by
-- proof
  apply StatMech.FrontierA.triangularTorusCycle_edge_injective L p hp

/--
[triangularTorusCycle_xSeam_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularTorusCycle_xSeam_card_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  (p.edges.toFinset.filter (triangularTorusXSeamEdge L)).card = (Finset.univ.filter (fun k : Fin p.darts.length => StatMech.Onsager.ons_xWrap (triangularTorusXMovementDart L (triangularTorusCycleNativeDart L p k)))).card := by
-- proof
  apply StatMech.FrontierA.triangularTorusCycle_xSeam_card L p hp

/--
[triangularTorusCycle_ySeam_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularTorusCycle_ySeam_card_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  (p.edges.toFinset.filter (triangularTorusYSeamEdge L)).card = (Finset.univ.filter (fun k : Fin p.darts.length => StatMech.Onsager.ons_yWrap (triangularTorusYMovementDart L (triangularTorusCycleNativeDart L p k)))).card := by
-- proof
  apply StatMech.FrontierA.triangularTorusCycle_ySeam_card L p hp

/--
[triangularTorusCycle_evenHomology_eq_windingParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularTorusCycle_evenHomology_eq_windingParity_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
  {mx my : Int}
-- given
  (hp : p.IsCycle)
  (hdisplacement : ∑ k, triangularIntStep (triangularTorusCycleNativeDart L p k).2 = ((L : Int) * mx, (L : Int) * my)) :
-- imply
  triangularTorusEvenHomology L p.edges.toFinset = (StatMech.Onsager.ons_intParity mx, StatMech.Onsager.ons_intParity my) := by
-- proof
  apply StatMech.FrontierA.triangularTorusCycle_evenHomology_eq_windingParity L p hp mx my hdisplacement

/--
[triangularTorusCycle_surfaceHomology_eq_windingParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularTorusCycle_surfaceHomology_eq_windingParity_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
  {mx my : Int}
-- given
  (hp : p.IsCycle)
  (hdisplacement : ∑ k, triangularIntStep (triangularTorusCycleNativeDart L p k).2 = ((L : Int) * mx, (L : Int) * my)) :
-- imply
  surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L) p.edges.toFinset = (fun _ => StatMech.Onsager.ons_intParity mx, fun _ => StatMech.Onsager.ons_intParity my) := by
-- proof
  apply StatMech.FrontierA.triangularTorusCycle_surfaceHomology_eq_windingParity L p hp mx my hdisplacement

/--
[triangularTorusCycleNativeSite_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularTorusCycleNativeSite_injective_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ Function.Injective (fun k => (triangularTorusCycleNativeDart L p k).1) := by
-- proof
  apply StatMech.FrontierA.triangularTorusCycleNativeSite_injective L p hp

/--
[triangularTorusCycleLiftPos_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularTorusCycleLiftPos_injective_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ Function.Injective (triangularIntPos (fun k => (triangularTorusCycleNativeDart L p k).2)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusCycleLiftPos_injective L p hp

/--
[triangularIntPeriodicPos_reduce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularIntPeriodicPos_reduce_eq
  {n : Nat}
  [NeZero n]
  {L : Nat}
  {mx my : Int}
  {z : Int × Fin n}
-- given
  (direction : Fin n -> Fin 6)
  (hdisplacement : ∑ k, triangularIntStep (direction k) = ((L : Int) * mx, (L : Int) * my)) :
-- imply
  triangularIntReduce L (triangularIntPeriodicPos direction z) = triangularIntReduce L (triangularIntPos direction z.2) := by
-- proof
  apply StatMech.FrontierA.triangularIntPeriodicPos_reduce L direction mx my hdisplacement z

/--
[triangularTorusCyclePeriodicPos_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularTorusCyclePeriodicPos_injective_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
  {mx my : Int}
-- given
  (hp : p.IsCycle)
  (hdisplacement : ∑ k, triangularIntStep (triangularTorusCycleNativeDart L p k).2 = ((L : Int) * mx, (L : Int) * my))
  (hne : mx ≠ 0 ∨ my ≠ 0) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ Function.Injective (triangularIntPeriodicPos (fun k => (triangularTorusCycleNativeDart L p k).2)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusCyclePeriodicPos_injective L p hp mx my hdisplacement hne

/--
[triangularTorusCycleLiftPos_injective_of_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularTorusCycleLiftPos_injective_of_closed_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ forall (hclosed : ∑ k, triangularIntStep (triangularTorusCycleNativeDart L p k).2 = 0), Function.Injective (triangularIntPos (fun k => (triangularTorusCycleNativeDart L p k).2)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusCycleLiftPos_injective_of_closed L p hp

/--
[exists_triangularTorus_cycleTurnSum_eq_eight_mul_odd_of_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma exists_triangularTorus_cycleTurnSum_eq_eight_mul_odd_of_closed_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ forall (hclosed : ∑ k, triangularIntStep (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k)) = 0), exists m : Int, (∑ k, triangularTorusTurnExponent (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k)) (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p (k + 1)))) = 8 * (2 * m + 1) := by
-- proof
  apply StatMech.FrontierA.exists_triangularTorus_cycleTurnSum_eq_eight_mul_odd_of_closed L p hp

/--
[triangularTorus_cyclePhaseProduct_eq_neg_one_of_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean)
-/
@[path]
private lemma triangularTorus_cyclePhaseProduct_eq_neg_one_of_closed_eq
  {L : Nat}
  [Fact (2 < L)]
  {rho : Complex}
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ forall (hclosed : ∑ k, triangularIntStep (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k)) = 0), kwLoopPhaseProduct (triangularTorusGraphPhase L rho 1 1) (kwGraphCycleDartLoop p) = -1 := by
-- proof
  apply StatMech.FrontierA.triangularTorus_cyclePhaseProduct_eq_neg_one_of_closed L rho hrho p hp


-- created on 2026-10-23
