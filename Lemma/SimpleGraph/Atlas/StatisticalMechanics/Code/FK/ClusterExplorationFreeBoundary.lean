import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.ClusterExplorationFreeBoundary
open SimpleGraph StatMech StatMech.FK


/--
[clusterExploredVertex_of_openAdj_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterExplorationFreeBoundary.lean)
-/
@[path]
private lemma clusterExploredVertex_of_openAdj_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {rho : ConfigSpace (Sym2 V)}
  {roots : Finset V}
  {x y : V}
-- given
  (hxy : (openSub G rho).Adj x y)
  (hy : ClusterExploredVertex G rho roots y) :
-- imply
  ClusterExploredVertex G rho roots x := by
-- proof
  apply StatMech.FK.clusterExploredVertex_of_openAdj_right G rho roots hxy hy

/--
[not_clusterOutsideGraph_adj_from_unexplored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterExplorationFreeBoundary.lean)
-/
@[path]
private lemma not_clusterOutsideGraph_adj_from_unexplored_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {rho : ConfigSpace (Sym2 V)}
  {roots : Finset V}
  {x : ClusterUnexploredVertex G rho roots}
  {y : V} :
-- imply
  ¬ (ocd_outsideGraph G (Subtype.val : ClusterUnexploredVertex G rho roots -> V) (clusterNoBoundary : V -> Prop) rho).Adj x.1 y := by
-- proof
  apply StatMech.FK.not_clusterOutsideGraph_adj_from_unexplored G rho roots x y

/--
[eq_of_clusterOutsideGraph_reachable_from_unexplored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterExplorationFreeBoundary.lean)
-/
@[path]
private lemma eq_of_clusterOutsideGraph_reachable_from_unexplored_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {rho : ConfigSpace (Sym2 V)}
  {roots : Finset V}
  {x y : V}
-- given
  (hx : ¬ ClusterExploredVertex G rho roots x)
  (hreach : (ocd_outsideGraph G (Subtype.val : ClusterUnexploredVertex G rho roots -> V) (clusterNoBoundary : V -> Prop) rho).Reachable x y) :
-- imply
  x = y := by
-- proof
  apply StatMech.FK.eq_of_clusterOutsideGraph_reachable_from_unexplored G rho roots hx hreach

/--
[clusterExploration_inducedWiring_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterExplorationFreeBoundary.lean)
-/
@[path]
private lemma clusterExploration_inducedWiring_eq_bot_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {rho : ConfigSpace (Sym2 V)}
  {roots : Finset V} :
-- imply
  ocd_inducedWiring G (Subtype.val : ClusterUnexploredVertex G rho roots -> V) (clusterNoBoundary : V -> Prop) rho = (⊥ : SimpleGraph (ClusterUnexploredVertex G rho roots)) := by
-- proof
  apply StatMech.FK.clusterExploration_inducedWiring_eq_bot G rho roots

/--
[clusterExploration_condBcProb_eq_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterExplorationFreeBoundary.lean)
-/
@[path]
private lemma clusterExploration_condBcProb_eq_free_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {rho : ConfigSpace (Sym2 V)}
  {roots : Finset V}
  {p q : Real}
  {omega : ConfigSpace (Sym2 (ClusterUnexploredVertex G rho roots))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  condBcProb G (StatMech.Lattice.boundaryCliqueGraph (clusterNoBoundary : V -> Prop)) p q (clusterUnexploredPairEdges G rho roots) rho (@ocd_psiExt (ClusterUnexploredVertex G rho roots) V (instFintypeClusterUnexploredVertex G rho roots) (by infer_instance) (Subtype.val : ClusterUnexploredVertex G rho roots -> V) rho omega) = fkProb (clusterUnexploredGraph G rho roots) p q omega := by
-- proof
  apply StatMech.FK.clusterExploration_condBcProb_eq_free G rho roots hp hp1 hq omega

/--
[clusterExploration_condBcProb_innerEvent_eq_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterExplorationFreeBoundary.lean)
-/
@[path]
private lemma clusterExploration_condBcProb_innerEvent_eq_free_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {rho : ConfigSpace (Sym2 V)}
  {roots : Finset V}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 (ClusterUnexploredVertex G rho roots)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∑ sigma : ConfigSpace (Sym2 V), (ocd_innerRestrict (Subtype.val : ClusterUnexploredVertex G rho roots -> V) ⁻¹' A).indicator (fun _ => (1 : Real)) sigma * condBcProb G (StatMech.Lattice.boundaryCliqueGraph (clusterNoBoundary : V -> Prop)) p q (clusterUnexploredPairEdges G rho roots) rho sigma) = ∑ omega, A.indicator (fun _ => (1 : Real)) omega * fkProb (clusterUnexploredGraph G rho roots) p q omega := by
-- proof
  apply StatMech.FK.clusterExploration_condBcProb_innerEvent_eq_free G rho roots hp hp1 hq A


-- created on 2026-10-23
