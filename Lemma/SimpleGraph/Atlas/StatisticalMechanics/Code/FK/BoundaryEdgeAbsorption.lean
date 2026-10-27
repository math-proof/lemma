import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
open Finset SimpleGraph StatMech StatMech.FK


/--
[activeGraphRestrict_configSplit_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean)
-/
@[path]
private lemma activeGraphRestrict_configSplit_symm_eq
  [Fintype V]
  [DecidableEq V]
  {rho : ConfigSpace G.edgeSet}
  {xi : ConfigSpace (AddedEdge G H)}
-- given
  (hGH : G <= H) :
-- imply
  activeGraphRestrict G H hGH ((activeGraphConfigSplitEquiv G H hGH).symm (rho, xi)) = rho := by
-- proof
  apply StatMech.FK.activeGraphRestrict_configSplit_symm hGH rho xi

/--
[openSub_extendActive_restrictActive_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean)
-/
@[path]
private lemma openSub_extendActive_restrictActive_eq_eq
  [Fintype V]
  [DecidableEq V]
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  openSub G (extendActive G (restrictActive G omega)) = openSub G omega := by
-- proof
  apply StatMech.FK.openSub_extendActive_restrictActive_eq omega

/--
[wiredGraph_eq_of_le_sup_boundaryClique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean)
-/
@[path]
private lemma wiredGraph_eq_of_le_sup_boundaryClique_eq
  [Fintype V]
  [DecidableEq V]
  {eta : ConfigSpace H.edgeSet}
-- given
  (hGH : G <= H)
  (habsorb : H <= G ⊔ boundaryCliqueGraph boundary) :
-- imply
  wiredGraph H boundary (extendActive H eta) = wiredGraph G boundary (extendActive G (activeGraphRestrict G H hGH eta)) := by
-- proof
  apply StatMech.FK.wiredGraph_eq_of_le_sup_boundaryClique hGH habsorb eta

/--
[numClustersWired_eq_of_le_sup_boundaryClique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean)
-/
@[path]
private lemma numClustersWired_eq_of_le_sup_boundaryClique_eq
  [Fintype V]
  [DecidableEq V]
  {eta : ConfigSpace H.edgeSet}
-- given
  (hGH : G <= H)
  (habsorb : H <= G ⊔ boundaryCliqueGraph boundary) :
-- imply
  numClustersWired H boundary (extendActive H eta) = numClustersWired G boundary (extendActive G (activeGraphRestrict G H hGH eta)) := by
-- proof
  apply StatMech.FK.numClustersWired_eq_of_le_sup_boundaryClique hGH habsorb eta

/--
[edgeProductW_configSplit_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean)
-/
@[path]
private lemma edgeProductW_configSplit_symm_eq
  [Fintype V]
  [DecidableEq V]
  {p : Real}
  {rho : ConfigSpace G.edgeSet}
  {xi : ConfigSpace (AddedEdge G H)}
-- given
  (hGH : G <= H) :
-- imply
  edgeProductW H (fun _ => p) (extendActive H ((activeGraphConfigSplitEquiv G H hGH).symm (rho, xi))) = edgeProductW G (fun _ => p) (extendActive G rho) * ∏ e : AddedEdge G H, if xi e then p else 1 - p := by
-- proof
  apply StatMech.FK.edgeProductW_configSplit_symm hGH p rho xi

/--
[addedBernoulliWeight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean)
-/
@[path]
private lemma addedBernoulliWeight_sum_eq
  [Fintype V]
  [DecidableEq V]
  {p : Real} :
-- imply
  (∑ xi : ConfigSpace (AddedEdge G H), (∏ e, if xi e then p else 1 - p)) = 1 := by
-- proof
  apply StatMech.FK.addedBernoulliWeight_sum p

/--
[activeBCWeight_configSplit_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean)
-/
@[path]
private lemma activeBCWeight_configSplit_symm_eq
  [Fintype V]
  [DecidableEq V]
  {p q : Real}
  {rho : ConfigSpace G.edgeSet}
  {xi : ConfigSpace (AddedEdge G H)}
-- given
  (hGH : G <= H)
  (habsorb : H <= G ⊔ boundaryCliqueGraph boundary) :
-- imply
  activeBCWeight H (boundaryCliqueGraph boundary) (fun _ => p) q ((activeGraphConfigSplitEquiv G H hGH).symm (rho, xi)) = (∏ e, if xi e then p else 1 - p) * activeBCWeight G (boundaryCliqueGraph boundary) (fun _ => p) q rho := by
-- proof
  apply StatMech.FK.activeBCWeight_configSplit_symm hGH habsorb p q rho xi

/--
[activeBCZ_eq_of_le_sup_boundaryClique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean)
-/
@[path]
private lemma activeBCZ_eq_of_le_sup_boundaryClique_eq
  [Fintype V]
  [DecidableEq V]
  {p q : Real}
-- given
  (hGH : G <= H)
  (habsorb : H <= G ⊔ boundaryCliqueGraph boundary) :
-- imply
  activeBCZ H (boundaryCliqueGraph boundary) (fun _ => p) q = activeBCZ G (boundaryCliqueGraph boundary) (fun _ => p) q := by
-- proof
  apply StatMech.FK.activeBCZ_eq_of_le_sup_boundaryClique hGH habsorb p q

/--
[activeBCNumer_eq_of_le_sup_boundaryClique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean)
-/
@[path]
private lemma activeBCNumer_eq_of_le_sup_boundaryClique_eq
  [Fintype V]
  [DecidableEq V]
  {p q : Real}
-- given
  (hGH : G <= H)
  (habsorb : H <= G ⊔ boundaryCliqueGraph boundary)
  (f : ConfigSpace G.edgeSet -> Real) :
-- imply
  activeBCNumer H (boundaryCliqueGraph boundary) (fun _ => p) q (fun eta => f (activeGraphRestrict G H hGH eta)) = activeBCNumer G (boundaryCliqueGraph boundary) (fun _ => p) q f := by
-- proof
  apply StatMech.FK.activeBCNumer_eq_of_le_sup_boundaryClique hGH habsorb p q f

/--
[activeBCMean_eq_of_le_sup_boundaryClique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean)
-/
@[path]
private lemma activeBCMean_eq_of_le_sup_boundaryClique_eq
  [Fintype V]
  [DecidableEq V]
  {p q : Real}
-- given
  (hGH : G <= H)
  (habsorb : H <= G ⊔ boundaryCliqueGraph boundary)
  (f : ConfigSpace G.edgeSet -> Real) :
-- imply
  activeBCMean H (boundaryCliqueGraph boundary) (fun _ => p) q (fun eta => f (activeGraphRestrict G H hGH eta)) = activeBCMean G (boundaryCliqueGraph boundary) (fun _ => p) q f := by
-- proof
  apply StatMech.FK.activeBCMean_eq_of_le_sup_boundaryClique hGH habsorb p q f

/--
[exists_boundary_reachable_of_sup_boundaryClique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean)
-/
@[path]
private lemma exists_boundary_reachable_of_sup_boundaryClique_eq
  [Fintype V]
  [DecidableEq V]
  {A : SimpleGraph V}
  [DecidableRel A.Adj]
  {root : V}
  {y : V}
-- given
  (hroot : ¬ boundary root)
  (hy : boundary y)
  (hreach : (A ⊔ boundaryCliqueGraph boundary).Reachable root y) :
-- imply
  ∃ z : V, boundary z ∧ A.Reachable root z := by
-- proof
  apply StatMech.FK.exists_boundary_reachable_of_sup_boundaryClique A hroot hy hreach

/--
[boundaryReachable_iff_of_le_sup_boundaryClique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean)
-/
@[path]
private lemma boundaryReachable_iff_of_le_sup_boundaryClique_eq
  [Fintype V]
  [DecidableEq V]
  {root : V}
  {eta : ConfigSpace H.edgeSet}
-- given
  (hGH : G <= H)
  (habsorb : H <= G ⊔ boundaryCliqueGraph boundary)
  (hroot : ¬ boundary root) :
-- imply
  (∃ y : V, boundary y ∧ (openSub H (extendActive H eta)).Reachable root y) ↔ ∃ y : V, boundary y ∧ (openSub G (extendActive G (activeGraphRestrict G H hGH eta))).Reachable root y := by
-- proof
  apply StatMech.FK.boundaryReachable_iff_of_le_sup_boundaryClique hGH habsorb hroot eta

/--
[finiteRootBoundaryEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean)
-/
@[path]
private lemma finiteRootBoundaryEvent_isIncreasing_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {K : SimpleGraph W}
  {root : W}
-- given
  (bdry : W → Prop) :
-- imply
  IsIncreasing (finiteRootBoundaryEvent K bdry root) := by
-- proof
  apply StatMech.FK.finiteRootBoundaryEvent_isIncreasing K bdry root

/--
[finiteWiredEventMass_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean)
-/
@[path]
private lemma finiteWiredEventMass_mono_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq Vin]
  [DecidableEq Vout]
  [Fintype W]
  [DecidableEq W]
  {K : SimpleGraph W}
  [DecidableRel K.Adj]
  [DecidablePred bdry]
  {p q : Real}
  {A B : Set (ConfigSpace (Sym2 W))}
-- given
  (bdry : W → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hAB : A ⊆ B) :
-- imply
  finiteWiredEventMass K bdry p q A ≤ finiteWiredEventMass K bdry p q B := by
-- proof
  apply StatMech.FK.finiteWiredEventMass_mono K bdry hp hp1 hq hAB

/--
[ocd_boundaryReach_of_outerBoundaryReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean)
-/
@[path]
private lemma ocd_boundaryReach_of_outerBoundaryReach_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {rho : ConfigSpace (Sym2 Vout)}
  {root : Vin}
-- given
  (hadj : ocd_AdjMatch Gin Gout incl)
  (hmargin : ∀ x, ¬ bdryOut (incl x))
  (hcross : ∀ x c, Gout.Adj (incl x) c → c ∉ Set.range incl → bdryIn x)
  (hreach : ∃ y, bdryOut y ∧ (openSub Gout rho).Reachable (incl root) y) :
-- imply
  ∃ z, bdryIn z ∧ (openSub Gin (ocd_innerRestrict incl rho)).Reachable root z := by
-- proof
  apply StatMech.FK.ocd_boundaryReach_of_outerBoundaryReach hadj hmargin hcross rho root hreach

/--
[outerRootBoundaryEvent_subset_innerRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean)
-/
@[path]
private lemma outerRootBoundaryEvent_subset_innerRestrict_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {root : Vin}
-- given
  (hadj : ocd_AdjMatch Gin Gout incl)
  (hmargin : ∀ x, ¬ bdryOut (incl x))
  (hcross : ∀ x c, Gout.Adj (incl x) c → c ∉ Set.range incl → bdryIn x) :
-- imply
  finiteRootBoundaryEvent Gout bdryOut (incl root) ⊆ ocd_innerRestrict incl ⁻¹' finiteRootBoundaryEvent Gin bdryIn root := by
-- proof
  apply StatMech.FK.outerRootBoundaryEvent_subset_innerRestrict hadj hmargin hcross root


-- created on 2026-10-23
