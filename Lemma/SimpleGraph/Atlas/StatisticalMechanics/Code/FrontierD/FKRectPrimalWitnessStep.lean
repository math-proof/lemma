import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalWitnessStep.Part2
open SimpleGraph StatMech StatMech.FK StatMech.FrontierD


/--
[ocd_condBcProb_innerEvent_eq_of_psiExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalWitnessStep.lean)
-/
@[path]
private lemma ocd_condBcProb_innerEvent_eq_of_psiExt_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {iota : Vin → Vout}
  {bdryOut : Vout → Prop}
  [DecidablePred bdryOut]
  {p q : Real}
  {psi : ConfigSpace (Sym2 Vout)}
  {mu : ConfigSpace (Sym2 Vin) → Real}
  {A : Set (ConfigSpace (Sym2 Vin))}
-- given
  (hiota : Function.Injective iota)
  (hadj : ocd_AdjMatch Gin Gout iota)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hmu : ∀ omega, condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q (ocd_innerEdgeFinset iota) psi (ocd_psiExt iota psi omega) = mu omega) :
-- imply
  (∑ rho : ConfigSpace (Sym2 Vout), (ocd_innerRestrict iota ⁻¹' A).indicator (fun _ => (1 : Real)) rho * condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q (ocd_innerEdgeFinset iota) psi rho) = ∑ omega : ConfigSpace (Sym2 Vin), A.indicator (fun _ => (1 : Real)) omega * mu omega := by
-- proof
  apply StatMech.FK.ocd_condBcProb_innerEvent_eq_of_psiExt hiota hadj hp hp1 hq psi mu hmu A

/--
[ocd_outsideGraph_congr_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalWitnessStep.lean)
-/
@[path]
private lemma ocd_outsideGraph_congr_edges_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {iota : Vin → Vout}
  [DecidablePred bdryOut]
  {psi psi' : ConfigSpace (Sym2 Vout)}
-- given
  (bdryOut : Vout → Prop)
  (h : ∀ x y, Gout.Adj x y → psi s(x, y) = psi' s(x, y)) :
-- imply
  ocd_outsideGraph Gout iota bdryOut psi = ocd_outsideGraph Gout iota bdryOut psi' := by
-- proof
  apply StatMech.FK.ocd_outsideGraph_congr_edges Gout iota bdryOut psi psi' h

/--
[ocd_inducedWiring_congr_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalWitnessStep.lean)
-/
@[path]
private lemma ocd_inducedWiring_congr_edges_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {iota : Vin → Vout}
  [DecidablePred bdryOut]
  {psi psi' : ConfigSpace (Sym2 Vout)}
-- given
  (bdryOut : Vout → Prop)
  (h : ∀ x y, Gout.Adj x y → psi s(x, y) = psi' s(x, y)) :
-- imply
  ocd_inducedWiring Gout iota bdryOut psi = ocd_inducedWiring Gout iota bdryOut psi' := by
-- proof
  apply StatMech.FK.ocd_inducedWiring_congr_edges Gout iota bdryOut psi psi' h

/--
[bcProb_event_fibre_eq_mass_mul_cond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalWitnessStep.lean)
-/
@[path]
private lemma bcProb_event_fibre_eq_mass_mul_cond_eq
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  {p q : Real}
  {F : Finset (Sym2 V)}
  {psi : ConfigSpace (Sym2 V)}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∑ rho ∈ condFibre F psi, A.indicator (fun _ => (1 : Real)) rho * bcProb G C p q rho) = (∑ sigma ∈ condFibre F psi, bcProb G C p q sigma) * (∑ rho, A.indicator (fun _ => (1 : Real)) rho * condBcProb G C p q F psi rho) := by
-- proof
  apply StatMech.FK.bcProb_event_fibre_eq_mass_mul_cond G C hp hp1 hq F psi A

/--
[fkRectPrimalExploration_condMass_eq_freeUnexplored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalWitnessStep.lean)
-/
@[path]
private lemma fkRectPrimalExploration_condMass_eq_freeUnexplored_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 (FKRectPrimalUnexploredVertex R S eta)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∑ rho : ConfigSpace (Sym2 R.Vertex), (FK.ocd_innerRestrict (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex) ⁻¹' A).indicator (fun _ => (1 : Real)) rho * FK.condBcProb (fkRectCutGraph R) (StatMech.Lattice.boundaryCliqueGraph (fun _ : R.Vertex => False)) p q (fkRectPrimalUnexploredPairEdges R S eta) (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) rho) = ∑ omega : ConfigSpace (Sym2 (FKRectPrimalUnexploredVertex R S eta)), A.indicator (fun _ => (1 : Real)) omega * FK.fkProb (fkRectPrimalUnexploredInducedGraph R S eta) p q omega := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalExploration_condMass_eq_freeUnexplored R S eta hp hp1 hq A

/--
[fkRectPrimalExploration_condRightArm_le_boxBdry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalWitnessStep.lean)
-/
@[path]
private lemma fkRectPrimalExploration_condRightArm_le_boxBdry_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration}
  {source : FKRectPrimalUnexploredVertex R S eta}
  {p q : Real}
-- given
  (hleft : source.1.1 = fkRectLeftColumn R)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (∑ rho : ConfigSpace (Sym2 R.Vertex), (FK.ocd_innerRestrict (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex) ⁻¹' FKRectPrimalUnexploredRightArmEvent R S eta source).indicator (fun _ => (1 : Real)) rho * FK.condBcProb (fkRectCutGraph R) (StatMech.Lattice.boundaryCliqueGraph (fun _ : R.Vertex => False)) p q (fkRectPrimalUnexploredPairEdges R S eta) (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) rho) ≤ (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (FK.boxBdryConnEvent 2 (R.width - 2)) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalExploration_condRightArm_le_boxBdry R S eta source hleft hp hp1 hq

/--
[fkRectPrimalUnexploredInducedGraph_adj_of_insert_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalWitnessStep.lean)
-/
@[path]
private lemma fkRectPrimalUnexploredInducedGraph_adj_of_insert_reachable_eq
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
  let x' : FKRectPrimalUnexploredVertex R S eta := ⟨x, fkRectPrimalCrossing_insert_cluster_disjoint_explored R eta S i hi hwitness hix⟩ let y' : FKRectPrimalUnexploredVertex R S eta := ⟨y, fkRectPrimalCrossing_insert_cluster_disjoint_explored R eta S i hi hwitness (hix.trans hxy.reachable)⟩ (FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta) (FK.ocd_innerRestrict (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex) (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)))).Adj x' y' := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalUnexploredInducedGraph_adj_of_insert_reachable R eta S i hi hwitness hix hxy

/--
[fkRectPrimalUnexploredInduced_reachable_of_insert_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalWitnessStep.lean)
-/
@[path]
private lemma fkRectPrimalUnexploredInduced_reachable_of_insert_reachable_eq
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
  let source : FKRectPrimalUnexploredVertex R S eta := ⟨(fkRectLeftColumn R, i), fkRectPrimalCrossing_insert_source_not_explored R eta S i hi hwitness⟩ let target : FKRectPrimalUnexploredVertex R S eta := ⟨v, fkRectPrimalCrossing_insert_cluster_disjoint_explored R eta S i hi hwitness hiv⟩ (FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta) (FK.ocd_innerRestrict (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex) (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)))).Reachable source target := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalUnexploredInduced_reachable_of_insert_reachable R eta S i hi hwitness hiv

/--
[fkRectPrimalCrossingSourceWitnessCore_insert_imp_inducedRightArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalWitnessStep.lean)
-/
@[path]
private lemma fkRectPrimalCrossingSourceWitnessCore_insert_imp_inducedRightArm_eq
  {R : FKRectTorus}
  {eta : R.Configuration}
  {S : Finset (Fin R.height)}
  {i : Fin R.height}
-- given
  (hi : i ∉ S)
  (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta) :
-- imply
  let source : FKRectPrimalUnexploredVertex R S eta := ⟨(fkRectLeftColumn R, i), fkRectPrimalCrossing_insert_source_not_explored R eta S i hi hwitness⟩ FK.ocd_innerRestrict (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex) (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) ∈ FKRectPrimalUnexploredRightArmEvent R S eta source := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalCrossingSourceWitnessCore_insert_imp_inducedRightArm R eta S i hi hwitness


-- created on 2026-10-23
