import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part12
open Finset Complex StatMech StatMech.Universality StatMech.Universality.FKIsingDobrushinDomain StatMech.Universality.FKIsingDobrushinDomain.CaseTwoExplorationSwitchingLaw StatMech.Universality.FKIsingDobrushinDomain.CaseThreeExplorationSwitchingLaw StatMech.Universality.FKIsingDobrushinDomain.CaseThreeEastSouthExplorationSwitchingLaw StatMech.Universality.FKIsingDobrushinDomain.CaseOneExplorationSwitchingLaw StatMech.Universality.FKIsingDobrushinDomain.BalancedLocalSwitchingTable StatMech.Universality.FKIsingDobrushinDomain.ExhaustiveExplorationSwitchingLaw


/--
[fkIsingCriticalParameter_eq_sqrtTwo_mul_one_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma fkIsingCriticalParameter_eq_sqrtTwo_mul_one_sub_eq :
-- imply
  fkIsingCriticalParameter = Real.sqrt 2 * (1 - fkIsingCriticalParameter) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.fkIsingCriticalParameter_eq_sqrtTwo_mul_one_sub

/--
[windingPhase_eq_exp_turn_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma windingPhase_eq_exp_turn_mul_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {omega omega' : ConfigSpace (Sym2 P.V)}
  {e e' : M}
  {turn : Real}
-- given
  (h : D.winding omega' e' = D.winding omega e + turn) :
-- imply
  D.windingPhase omega' e' = Complex.exp (Complex.I * ((turn / 2 : Real) : Complex)) * D.windingPhase omega e := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.windingPhase_eq_exp_turn_mul D omega omega' e e' turn h

/--
[exp_isHalf_turn_pi_div_two_eq_isingLambda](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma exp_isHalf_turn_pi_div_two_eq_isingLambda_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M} :
-- imply
  Complex.exp (Complex.I * (((Real.pi / 2) / 2 : Real) : Complex)) = isingLambda := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.exp_isHalf_turn_pi_div_two_eq_isingLambda D

/--
[exp_isHalf_turn_pi_eq_isingLambda_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma exp_isHalf_turn_pi_eq_isingLambda_sq_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M} :
-- imply
  Complex.exp (Complex.I * ((Real.pi / 2 : Real) : Complex)) = isingLambda ^ 2 := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.exp_isHalf_turn_pi_eq_isingLambda_sq D

/--
[exp_isHalf_turn_neg_pi_div_two_eq_isingLambda_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma exp_isHalf_turn_neg_pi_div_two_eq_isingLambda_inv_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M} :
-- imply
  Complex.exp (Complex.I * (((-(Real.pi / 2)) / 2 : Real) : Complex)) = isingLambda⁻¹ := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.exp_isHalf_turn_neg_pi_div_two_eq_isingLambda_inv D

/--
[criticalMass_setOpen_eq_sqrtTwo_mul_setClosed_of_clusterCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma criticalMass_setOpen_eq_sqrtTwo_mul_setClosed_of_clusterCount_eq_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {e : Sym2 P.V}
  {omega : ConfigSpace (Sym2 P.V)}
-- given
  (he : e ∈ P.G.edgeFinset)
  (hcluster : numClustersBC P.G D.wiring (setOpen e omega) = numClustersBC P.G D.wiring (setClosed e omega)) :
-- imply
  D.criticalMass (setOpen e omega) = Real.sqrt 2 * D.criticalMass (setClosed e omega) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.criticalMass_setOpen_eq_sqrtTwo_mul_setClosed_of_clusterCount_eq D he omega hcluster

/--
[sqrtTwo_mul_criticalMass_setOpen_eq_setClosed_of_clusterMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma sqrtTwo_mul_criticalMass_setOpen_eq_setClosed_of_clusterMerge_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {e : Sym2 P.V}
  {omega : ConfigSpace (Sym2 P.V)}
-- given
  (he : e ∈ P.G.edgeFinset)
  (hcluster : numClustersBC P.G D.wiring (setClosed e omega) = numClustersBC P.G D.wiring (setOpen e omega) + 1) :
-- imply
  Real.sqrt 2 * D.criticalMass (setOpen e omega) = D.criticalMass (setClosed e omega) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.sqrtTwo_mul_criticalMass_setOpen_eq_setClosed_of_clusterMerge D he omega hcluster

/--
[numClustersBC_setClosed_eq_setOpen_add_one_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma numClustersBC_setClosed_eq_setOpen_add_one_of_not_reachable_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {a b : P.V}
  {omega : ConfigSpace (Sym2 P.V)}
-- given
  (hab : P.G.Adj a b)
  (hnot : ¬(openSub P.G (setClosed s(a, b) omega) ⊔ D.wiring).Reachable a b) :
-- imply
  numClustersBC P.G D.wiring (setClosed s(a, b) omega) = numClustersBC P.G D.wiring (setOpen s(a, b) omega) + 1 := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.numClustersBC_setClosed_eq_setOpen_add_one_of_not_reachable D a b hab omega hnot

/--
[numClustersBC_setOpen_eq_setClosed_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma numClustersBC_setOpen_eq_setClosed_of_reachable_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {a b : P.V}
  {omega : ConfigSpace (Sym2 P.V)}
-- given
  (hab : P.G.Adj a b)
  (hreach : (openSub P.G (setClosed s(a, b) omega) ⊔ D.wiring).Reachable a b) :
-- imply
  numClustersBC P.G D.wiring (setOpen s(a, b) omega) = numClustersBC P.G D.wiring (setClosed s(a, b) omega) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.numClustersBC_setOpen_eq_setClosed_of_reachable D a b hab omega hreach

/--
[localEdgeFlip_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma localEdgeFlip_involutive_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {e : Sym2 P.V} :
-- imply
  Function.Involutive (localEdgeFlip (P := P) e) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.localEdgeFlip_involutive D e

/--
[pair_with_localEdgeFlip_eq_closed_add_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma pair_with_localEdgeFlip_eq_closed_add_open_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {e : Sym2 P.V}
  {omega : ConfigSpace (Sym2 P.V)}
-- given
  (f : ConfigSpace (Sym2 P.V) -> Complex) :
-- imply
  f omega + f (localEdgeFlipEquiv e omega) = f (setClosed e omega) + f (setOpen e omega) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.pair_with_localEdgeFlip_eq_closed_add_open D e f omega

/--
[crossingEdge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma crossingEdge_mem_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {L : D.CaseTwoExplorationSwitchingLaw} :
-- imply
  L.crossingEdge ∈ P.G.edgeFinset := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.CaseTwoExplorationSwitchingLaw.crossingEdge_mem D L

/--
[clusterMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma clusterMerge_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {L : D.CaseTwoExplorationSwitchingLaw}
  {omega : ConfigSpace (Sym2 P.V)} :
-- imply
  numClustersBC P.G D.wiring (setClosed L.crossingEdge omega) = numClustersBC P.G D.wiring (setOpen L.crossingEdge omega) + 1 := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.CaseTwoExplorationSwitchingLaw.clusterMerge D L omega

/--
[crossingEdge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma crossingEdge_mem_eq_2
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {L : D.CaseThreeExplorationSwitchingLaw} :
-- imply
  L.crossingEdge ∈ P.G.edgeFinset := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.CaseThreeExplorationSwitchingLaw.crossingEdge_mem D L

/--
[clusterCountEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma clusterCountEq_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {L : D.CaseThreeExplorationSwitchingLaw}
  {omega : ConfigSpace (Sym2 P.V)} :
-- imply
  numClustersBC P.G D.wiring (setOpen L.crossingEdge omega) = numClustersBC P.G D.wiring (setClosed L.crossingEdge omega) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.CaseThreeExplorationSwitchingLaw.clusterCountEq D L omega

/--
[crossingEdge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma crossingEdge_mem_eq_3
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {L : D.CaseThreeEastSouthExplorationSwitchingLaw} :
-- imply
  L.crossingEdge ∈ P.G.edgeFinset := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.CaseThreeEastSouthExplorationSwitchingLaw.crossingEdge_mem D L

/--
[clusterCountEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma clusterCountEq_eq_2
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {L : D.CaseThreeEastSouthExplorationSwitchingLaw}
  {omega : ConfigSpace (Sym2 P.V)} :
-- imply
  numClustersBC P.G D.wiring (setOpen L.crossingEdge omega) = numClustersBC P.G D.wiring (setClosed L.crossingEdge omega) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.CaseThreeEastSouthExplorationSwitchingLaw.clusterCountEq D L omega

/--
[fermionicObservable_sHolo_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma fermionicObservable_sHolo_relation_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {L : D.CaseOneExplorationSwitchingLaw} :
-- imply
  D.fermionicObservable (L.edges 0) + D.fermionicObservable (L.edges 1) = D.fermionicObservable (L.edges 2) + D.fermionicObservable (L.edges 3) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.CaseOneExplorationSwitchingLaw.fermionicObservable_sHolo_relation D L

/--
[fermionicObservable_contour_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma fermionicObservable_contour_relation_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {T : D.BalancedLocalSwitchingTable} :
-- imply
  D.fermionicObservable (T.edges 0) - D.fermionicObservable (T.edges 1) = Complex.I * (D.fermionicObservable (T.edges 2) - D.fermionicObservable (T.edges 3)) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.BalancedLocalSwitchingTable.fermionicObservable_contour_relation D T

/--
[fermionicObservable_contour_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma fermionicObservable_contour_relation_eq_2
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {L : D.CaseTwoExplorationSwitchingLaw} :
-- imply
  D.fermionicObservable (L.edges 0) - D.fermionicObservable (L.edges 1) = Complex.I * (D.fermionicObservable (L.edges 2) - D.fermionicObservable (L.edges 3)) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.CaseTwoExplorationSwitchingLaw.fermionicObservable_contour_relation D L

/--
[fermionicObservable_contour_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma fermionicObservable_contour_relation_eq_3
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {L : D.CaseThreeExplorationSwitchingLaw} :
-- imply
  D.fermionicObservable (L.edges 0) - D.fermionicObservable (L.edges 1) = Complex.I * (D.fermionicObservable (L.edges 2) - D.fermionicObservable (L.edges 3)) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.CaseThreeExplorationSwitchingLaw.fermionicObservable_contour_relation D L

/--
[fermionicObservable_contour_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma fermionicObservable_contour_relation_eq_4
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {L : D.CaseThreeEastSouthExplorationSwitchingLaw} :
-- imply
  D.fermionicObservable (L.edges 0) - D.fermionicObservable (L.edges 1) = Complex.I * (D.fermionicObservable (L.edges 2) - D.fermionicObservable (L.edges 3)) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.CaseThreeEastSouthExplorationSwitchingLaw.fermionicObservable_contour_relation D L

/--
[fermionicObservable_contour_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean)
-/
@[path]
private lemma fermionicObservable_contour_relation_eq_5
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {L : D.ExhaustiveExplorationSwitchingLaw} :
-- imply
  D.fermionicObservable (L.edges 0) - D.fermionicObservable (L.edges 1) = Complex.I * (D.fermionicObservable (L.edges 2) - D.fermionicObservable (L.edges 3)) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.ExhaustiveExplorationSwitchingLaw.fermionicObservable_contour_relation D L


-- created on 2026-10-23
