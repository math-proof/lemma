import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part8
open StatMech StatMech.FrontierD


/--
[fkRectCriticalEventMass_eq_finiteEventMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_eq_finiteEventMass_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration} :
-- imply
  fkRectCriticalEventMass R q A = StatMech.Probability.finiteEventMass (fun eta => fkRectCriticalRandomClusterProb R q eta) A := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_eq_finiteEventMass R q A

/--
[mem_fkRectTorusCutGraphEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma mem_fkRectTorusCutGraphEdges_eq
  {R : FKRectTorus}
  {a : R.EdgeIndex} :
-- imply
  fkRectTorusIndexedEdge R a ∈ fkRectTorusCutGraphEdges R ↔ a ∈ fkRectTorusCutEdges R := by
-- proof
  apply StatMech.FrontierD.mem_fkRectTorusCutGraphEdges R a

/--
[fkRectFullGraphConfiguration_forceCut_eq_false_of_cutEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectFullGraphConfiguration_forceCut_eq_false_of_cutEdge_eq
  {R : FKRectTorus}
  {eta : R.Configuration}
  {e : Sym2 R.Vertex}
-- given
  (he : e ∈ fkRectTorusCutGraphEdges R) :
-- imply
  fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta) e = false := by
-- proof
  apply StatMech.FrontierD.fkRectFullGraphConfiguration_forceCut_eq_false_of_cutEdge R eta he

/--
[fkRectCutGraph_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectCutGraph_adj_iff_eq
  {R : FKRectTorus}
  {x y : R.Vertex} :
-- imply
  (fkRectCutGraph R).Adj x y ↔ (fkRectTorusGraph R).Adj x y ∧ s(x, y) ∉ fkRectTorusCutGraphEdges R := by
-- proof
  apply StatMech.FrontierD.fkRectCutGraph_adj_iff R x y

/--
[fkRectPrimalUnexploredInducedGraph_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectPrimalUnexploredInducedGraph_adjMatch_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration} :
-- imply
  FK.ocd_AdjMatch (fkRectPrimalUnexploredInducedGraph R S eta) (fkRectCutGraph R) (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalUnexploredInducedGraph_adjMatch R S eta

/--
[fkRectPrimalExploration_cutGraph_condFkProb_eq_induced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectPrimalExploration_cutGraph_condFkProb_eq_induced_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta omega : R.Configuration}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.condFkProb (fkRectCutGraph R) p q (fkRectPrimalUnexploredPairEdges R S eta) (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) (fkRectFullGraphConfiguration R omega) = FK.inducedFkProb (fkRectCutGraph R) p q (fkRectPrimalUnexploredPairEdges R S eta) (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) (fkRectFullGraphConfiguration R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalExploration_cutGraph_condFkProb_eq_induced R S eta omega hp hp1 hq

/--
[fkRectPrimalInsertionArmEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectPrimalInsertionArmEvent_isIncreasing_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {i : Fin R.height}
  {eta : R.Configuration} :
-- imply
  IsIncreasing (FKRectPrimalInsertionArmEvent R S i eta) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalInsertionArmEvent_isIncreasing R S i eta

/--
[fkRectPrimalUnexploredGraph_adj_of_insert_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectPrimalUnexploredGraph_adj_of_insert_reachable_eq
  {R : FKRectTorus}
  {eta : R.Configuration}
  {S : Finset (Fin R.height)}
  {i : Fin R.height}
  {x y : R.Vertex}
-- given
  (hi : i ∉ S)
  (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta)
  (hix : (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Reachable (fkRectLeftColumn R, i) x)
  (hxy : (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Adj x y) :
-- imply
  (FK.openSub (fkRectPrimalUnexploredGraph R S eta) (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))).Adj x y := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalUnexploredGraph_adj_of_insert_reachable R eta S i hi hwitness hix hxy

/--
[fkRectPrimalUnexplored_reachable_of_insert_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectPrimalUnexplored_reachable_of_insert_reachable_eq
  {R : FKRectTorus}
  {eta : R.Configuration}
  {S : Finset (Fin R.height)}
  {i : Fin R.height}
  {v : R.Vertex}
-- given
  (hi : i ∉ S)
  (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta)
  (hiv : (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Reachable (fkRectLeftColumn R, i) v) :
-- imply
  (FK.openSub (fkRectPrimalUnexploredGraph R S eta) (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))).Reachable (fkRectLeftColumn R, i) v := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalUnexplored_reachable_of_insert_reachable R eta S i hi hwitness hiv

/--
[fkRectPrimalCrossingSourceWitnessCore_insert_imp_arm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectPrimalCrossingSourceWitnessCore_insert_imp_arm_eq
  {R : FKRectTorus}
  {eta : R.Configuration}
  {S : Finset (Fin R.height)}
  {i : Fin R.height}
-- given
  (hi : i ∉ S)
  (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta) :
-- imply
  fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta) ∈ FKRectPrimalInsertionArmEvent R S i eta := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalCrossingSourceWitnessCore_insert_imp_arm R eta S i hi hwitness

/--
[fkRectPrimalCrossing_insert_cluster_disjoint_explored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectPrimalCrossing_insert_cluster_disjoint_explored_eq
  {R : FKRectTorus}
  {eta : R.Configuration}
  {S : Finset (Fin R.height)}
  {i : Fin R.height}
  {v : R.Vertex}
-- given
  (hi : i ∉ S)
  (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta)
  (hiv : (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Reachable (fkRectLeftColumn R, i) v) :
-- imply
  ¬ FKRectPrimalExploredVertex R S eta v := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalCrossing_insert_cluster_disjoint_explored R eta S i hi hwitness hiv

/--
[fkRectPrimalCrossing_insert_source_not_explored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectPrimalCrossing_insert_source_not_explored_eq
  {R : FKRectTorus}
  {eta : R.Configuration}
  {S : Finset (Fin R.height)}
  {i : Fin R.height}
-- given
  (hi : i ∉ S)
  (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta) :
-- imply
  ¬ FKRectPrimalExploredVertex R S eta (fkRectLeftColumn R, i) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalCrossing_insert_source_not_explored R eta S i hi hwitness

/--
[fkRectPrimalExploredVertex_of_openAdj_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectPrimalExploredVertex_of_openAdj_right_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration}
  {x y : R.Vertex}
-- given
  (hxy : (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Adj x y)
  (hy : FKRectPrimalExploredVertex R S eta y) :
-- imply
  FKRectPrimalExploredVertex R S eta x := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalExploredVertex_of_openAdj_right R S eta hxy hy

/--
[not_primalExplorationOutsideOpenGraph_adj_of_not_explored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma not_primalExplorationOutsideOpenGraph_adj_of_not_explored_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration}
  {x y : R.Vertex}
-- given
  (hx : ¬ FKRectPrimalExploredVertex R S eta x) :
-- imply
  ¬ (fkRectPrimalExplorationOutsideOpenGraph R S eta).Adj x y := by
-- proof
  apply StatMech.FrontierD.not_primalExplorationOutsideOpenGraph_adj_of_not_explored R S eta hx

/--
[not_primalExplorationInducedBoundary_adj_of_not_explored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma not_primalExplorationInducedBoundary_adj_of_not_explored_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration}
  {x y : R.Vertex}
-- given
  (hx : ¬ FKRectPrimalExploredVertex R S eta x)
  (hy : ¬ FKRectPrimalExploredVertex R S eta y) :
-- imply
  ¬ (fkRectPrimalExplorationInducedBoundary R S eta).Adj x y := by
-- proof
  apply StatMech.FrontierD.not_primalExplorationInducedBoundary_adj_of_not_explored R S eta hx hy

/--
[not_ocdOutsideGraph_adj_from_unexplored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma not_ocdOutsideGraph_adj_from_unexplored_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration}
  {x : FKRectPrimalUnexploredVertex R S eta}
  {y : R.Vertex} :
-- imply
  ¬ (FK.ocd_outsideGraph (fkRectCutGraph R) (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex) (fun _ : R.Vertex => False) (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))).Adj x.1 y := by
-- proof
  apply StatMech.FrontierD.not_ocdOutsideGraph_adj_from_unexplored R S eta x y

/--
[eq_of_ocdOutsideGraph_reachable_from_unexplored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma eq_of_ocdOutsideGraph_reachable_from_unexplored_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration}
  {x y : R.Vertex}
-- given
  (hx : ¬ FKRectPrimalExploredVertex R S eta x)
  (hreach : (FK.ocd_outsideGraph (fkRectCutGraph R) (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex) (fun _ : R.Vertex => False) (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))).Reachable x y) :
-- imply
  x = y := by
-- proof
  apply StatMech.FrontierD.eq_of_ocdOutsideGraph_reachable_from_unexplored R S eta hx hreach

/--
[fkRectPrimalExploration_ocdInducedWiring_le_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectPrimalExploration_ocdInducedWiring_le_bot_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration} :
-- imply
  FK.ocd_inducedWiring (fkRectCutGraph R) (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex) (fun _ : R.Vertex => False) (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) ≤ (⊥ : SimpleGraph (FKRectPrimalUnexploredVertex R S eta)) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalExploration_ocdInducedWiring_le_bot R S eta

/--
[fkRectPrimalExploration_ocdInducedWiring_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectPrimalExploration_ocdInducedWiring_eq_bot_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration} :
-- imply
  FK.ocd_inducedWiring (fkRectCutGraph R) (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex) (fun _ : R.Vertex => False) (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) = (⊥ : SimpleGraph (FKRectPrimalUnexploredVertex R S eta)) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalExploration_ocdInducedWiring_eq_bot R S eta

/--
[fkRectPrimalExploration_condBcProb_eq_freeUnexplored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectPrimalExploration_condBcProb_eq_freeUnexplored_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration}
  {p q : Real}
  {omega : ConfigSpace (Sym2 (FKRectPrimalUnexploredVertex R S eta))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.condBcProb (fkRectCutGraph R) (StatMech.Lattice.boundaryCliqueGraph (fun _ : R.Vertex => False)) p q (fkRectPrimalUnexploredPairEdges R S eta) (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) (@FK.ocd_psiExt (FKRectPrimalUnexploredVertex R S eta) R.Vertex (instFintypeFKRectPrimalUnexploredVertex R S eta) (by infer_instance) (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex) (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) omega) = FK.fkProb (fkRectPrimalUnexploredInducedGraph R S eta) p q omega := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalExploration_condBcProb_eq_freeUnexplored R S eta hp hp1 hq omega

/--
[fkRectPrimalExploration_condFkProb_eq_induced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectPrimalExploration_condFkProb_eq_induced_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta omega : R.Configuration}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.condFkProb (fkRectTorusGraph R) p q (fkRectPrimalUnexploredEdges R S eta) (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) (fkRectFullGraphConfiguration R omega) = FK.inducedFkProb (fkRectTorusGraph R) p q (fkRectPrimalUnexploredEdges R S eta) (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) (fkRectFullGraphConfiguration R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalExploration_condFkProb_eq_induced R S eta omega hp hp1 hq

/--
[exists_primalDualCrossingSourceWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma exists_primalDualCrossingSourceWitness_eq
  {R : FKRectTorus}
  {eta : R.Configuration}
  {n : Nat}
-- given
  (hclosed : FKRectCutClosedConfiguration R eta)
  (hn : n <= fkRectPrimalDualHorizontalCrossingClusterCount R eta) :
-- imply
  exists S : Finset (Fin (2 * R.height)), S.card = n /\ FKRectPrimalDualCrossingSourceWitness R S eta := by
-- proof
  apply StatMech.FrontierD.exists_primalDualCrossingSourceWitness R eta n hclosed hn

/--
[fkRectCritical_primalDualCrossingTail_le_choose_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectCritical_primalDualCrossingTail_le_choose_mul_pow_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
  {a : Real}
-- given
  (hq : 0 < q)
  (hn : 0 < n)
  (Witness : Finset (Fin (2 * R.height)) -> R.Configuration -> Prop)
  (hcover : forall eta : R.Configuration, FKRectCutClosedConfiguration R eta -> n <= fkRectPrimalDualHorizontalCrossingClusterCount R eta -> exists S : Finset (Fin (2 * R.height)), S.card = n /\ Witness S eta)
  (hmass : forall S : Finset (Fin (2 * R.height)), S.card = n -> fkRectCriticalEventMass R q {eta | Witness S eta} <= a ^ n) :
-- imply
  fkRectCriticalEventMass R q {eta | FKRectCutClosedConfiguration R eta ∧ n <= fkRectPrimalDualHorizontalCrossingClusterCount R eta} <= Nat.choose (2 * R.height) n * a ^ n := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_primalDualCrossingTail_le_choose_mul_pow R hq n hn a Witness hcover hmass

/--
[fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
  {a : Real}
-- given
  (hq : 0 < q)
  (Witness : Finset (Fin (2 * R.height)) -> R.Configuration -> Prop)
  (hcover : forall eta : R.Configuration, FKRectCutClosedConfiguration R eta -> n < fkRectPrimalDualHorizontalCrossingClusterCount R eta -> exists S : Finset (Fin (2 * R.height)), S.card = n + 1 /\ Witness S eta)
  (hmass : forall S : Finset (Fin (2 * R.height)), S.card = n + 1 -> fkRectCriticalEventMass R q {eta | Witness S eta} <= a ^ (n + 1)) :
-- imply
  fkRectCriticalEventMass R q {eta | FKRectCutClosedConfiguration R eta ∧ n < fkRectPrimalDualHorizontalCrossingClusterCount R eta} <= Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow R hq n a Witness hcover hmass

/--
[fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_of_sourceMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_of_sourceMass_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
  {a : Real}
-- given
  (hq : 0 < q)
  (hmass : forall S : Finset (Fin (2 * R.height)), S.card = n + 1 -> fkRectCriticalEventMass R q {eta | FKRectPrimalDualCrossingSourceWitness R S eta} <= a ^ (n + 1)) :
-- imply
  fkRectCriticalEventMass R q {eta | FKRectCutClosedConfiguration R eta ∧ n < fkRectPrimalDualHorizontalCrossingClusterCount R eta} <= Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_of_sourceMass R hq n a hmass

/--
[fkRectCritical_sourceWitnessMass_le_pow_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectCritical_sourceWitnessMass_le_pow_of_step_eq
  {R : FKRectTorus}
  {q : Real}
  {a : Real}
  {S : Finset (Fin (2 * R.height))}
-- given
  (hq : 0 < q)
  (ha : 0 <= a)
  (hstep : forall (T : Finset (Fin (2 * R.height))) (i : Fin (2 * R.height)), i ∉ T -> fkRectCriticalEventMass R q {eta | FKRectPrimalDualCrossingSourceWitness R (insert i T) eta} <= a * fkRectCriticalEventMass R q {eta | FKRectPrimalDualCrossingSourceWitness R T eta}) :
-- imply
  fkRectCriticalEventMass R q {eta | FKRectPrimalDualCrossingSourceWitness R S eta} <= a ^ S.card := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_sourceWitnessMass_le_pow_of_step R hq ha hstep S

/--
[fkRectCritical_sourceWitnessStep_of_cutFreeStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectCritical_sourceWitnessStep_of_cutFreeStep_eq
  {R : FKRectTorus}
  {q : Real}
  {a : Real}
  {T : Finset (Fin (2 * R.height))}
  {i : Fin (2 * R.height)}
-- given
  (hq : 1 <= q)
  (hstep : forall (T : Finset (Fin (2 * R.height))) (i : Fin (2 * R.height)), i ∉ T -> fkRectCriticalCutFreeEventMass R q {eta | FKRectPrimalDualCrossingSourceWitnessCore R (insert i T) eta} <= a * fkRectCriticalCutFreeEventMass R q {eta | FKRectPrimalDualCrossingSourceWitnessCore R T eta})
  (hi : i ∉ T) :
-- imply
  fkRectCriticalEventMass R q {eta | FKRectPrimalDualCrossingSourceWitness R (insert i T) eta} <= a * fkRectCriticalEventMass R q {eta | FKRectPrimalDualCrossingSourceWitness R T eta} := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_sourceWitnessStep_of_cutFreeStep R hq a hstep T i hi

/--
[fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_of_step_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
  {a : Real}
-- given
  (hq : 0 < q)
  (ha : 0 <= a)
  (hstep : forall (T : Finset (Fin (2 * R.height))) (i : Fin (2 * R.height)), i ∉ T -> fkRectCriticalEventMass R q {eta | FKRectPrimalDualCrossingSourceWitness R (insert i T) eta} <= a * fkRectCriticalEventMass R q {eta | FKRectPrimalDualCrossingSourceWitness R T eta}) :
-- imply
  fkRectCriticalEventMass R q {eta | FKRectCutClosedConfiguration R eta ∧ n < fkRectPrimalDualHorizontalCrossingClusterCount R eta} <= Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_of_step R hq n ha hstep

/--
[fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_of_cutFreeStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean)
-/
@[path]
private lemma fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_of_cutFreeStep_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
  {a : Real}
-- given
  (hq : 1 <= q)
  (ha : 0 <= a)
  (hstep : forall (T : Finset (Fin (2 * R.height))) (i : Fin (2 * R.height)), i ∉ T -> fkRectCriticalCutFreeEventMass R q {eta | FKRectPrimalDualCrossingSourceWitnessCore R (insert i T) eta} <= a * fkRectCriticalCutFreeEventMass R q {eta | FKRectPrimalDualCrossingSourceWitnessCore R T eta}) :
-- imply
  fkRectCriticalEventMass R q {eta | FKRectCutClosedConfiguration R eta ∧ n < fkRectPrimalDualHorizontalCrossingClusterCount R eta} <= Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_of_cutFreeStep R hq n ha hstep


-- created on 2026-10-23
