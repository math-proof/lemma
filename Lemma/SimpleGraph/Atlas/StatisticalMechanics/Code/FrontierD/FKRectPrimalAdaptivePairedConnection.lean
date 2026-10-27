import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptivePairedConnection.Part5
open MeasureTheory SimpleGraph StatMech.Lattice StatMech StatMech.FrontierD


/--
[fkRectPrimalAdaptive_condMass_eq_freeUnexplored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean)
-/
@[path]
private lemma fkRectPrimalAdaptive_condMass_eq_freeUnexplored_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {psi : ConfigSpace (Sym2 R.Vertex)}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 (FKRectPrimalUnexploredVertex R S (fkRectCutConfigOfFull R psi).1)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∑ rho : ConfigSpace (Sym2 R.Vertex), (FK.ocd_innerRestrict (Subtype.val : FKRectPrimalUnexploredVertex R S (fkRectCutConfigOfFull R psi).1 -> R.Vertex) ⁻¹' A).indicator (fun _ => (1 : Real)) rho * FK.condBcProb (fkRectCutGraph R) (boundaryCliqueGraph (fun _ : R.Vertex => False)) p q (fkRectPrimalAdaptiveInsideEdges R S psi) psi rho) = ∑ omega, A.indicator (fun _ => (1 : Real)) omega * FK.fkProb (fkRectPrimalUnexploredInducedGraph R S (fkRectCutConfigOfFull R psi).1) p q omega := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalAdaptive_condMass_eq_freeUnexplored R S psi hp hp1 hq A

/--
[fkRectPrimalAdaptivePairedConnectionEvent_condMass_le_boxConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean)
-/
@[path]
private lemma fkRectPrimalAdaptivePairedConnectionEvent_condMass_le_boxConn_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {i targetRow : Fin R.height}
  {psi : ConfigSpace (Sym2 R.Vertex)}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  (∑ rho : ConfigSpace (Sym2 R.Vertex), (FKRectPrimalAdaptivePairedConnectionEvent R S i targetRow psi).indicator (fun _ => (1 : Real)) rho * FK.condBcProb (fkRectCutGraph R) (boundaryCliqueGraph (fun _ : R.Vertex => False)) p q (fkRectPrimalAdaptiveInsideEdges R S psi) psi rho) <= (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (FK.boxConnEvent 2 (R.width + R.height) (fkRectVertexBoxEmbedding R (fkRectLeftColumn R, i)) (fkRectVertexBoxEmbedding R (fkRectRightColumn R, targetRow))) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalAdaptivePairedConnectionEvent_condMass_le_boxConn R S i targetRow psi hp hp1 hq

/--
[FKRectPrimalFullDistinctPairedWitness.toDistinctCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean)
-/
@[path]
private lemma toDistinctCrossing_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho : ConfigSpace (Sym2 R.Vertex)}
-- given
  (pair : Fin R.height -> Fin R.height)
  (h : FKRectPrimalFullDistinctPairedWitness R pair S rho) :
-- imply
  FKRectPrimalFullDistinctCrossingWitness R S rho := by
-- proof
  apply StatMech.FrontierD.FKRectPrimalFullDistinctPairedWitness.toDistinctCrossing R pair S rho h

/--
[fkRectPrimalFullDistinctPairedWitness_projection_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean)
-/
@[path]
private lemma fkRectPrimalFullDistinctPairedWitness_projection_iff_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho : ConfigSpace (Sym2 R.Vertex)}
-- given
  (pair : Fin R.height -> Fin R.height) :
-- imply
  FKRectPrimalFullDistinctPairedWitness R pair S (fkRectPrimalAdaptiveProjection R S rho) <-> FKRectPrimalFullDistinctPairedWitness R pair S rho := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullDistinctPairedWitness_projection_iff R pair S rho

/--
[fkRectPrimalFullDistinctPairedWitness_fibre_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean)
-/
@[path]
private lemma fkRectPrimalFullDistinctPairedWitness_fibre_iff_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho sigma : ConfigSpace (Sym2 R.Vertex)}
-- given
  (pair : Fin R.height -> Fin R.height)
  (hproj : fkRectPrimalAdaptiveProjection R S rho = fkRectPrimalAdaptiveProjection R S sigma) :
-- imply
  FKRectPrimalFullDistinctPairedWitness R pair S rho <-> FKRectPrimalFullDistinctPairedWitness R pair S sigma := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullDistinctPairedWitness_fibre_iff R pair S hproj

/--
[fkRectPrimalFullDistinctPairedWitness_insert_imp_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean)
-/
@[path]
private lemma fkRectPrimalFullDistinctPairedWitness_insert_imp_base_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {i : Fin R.height}
  {rho : ConfigSpace (Sym2 R.Vertex)}
-- given
  (pair : Fin R.height -> Fin R.height)
  (h : FKRectPrimalFullDistinctPairedWitness R pair (insert i S) rho) :
-- imply
  FKRectPrimalFullDistinctPairedWitness R pair S rho := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullDistinctPairedWitness_insert_imp_base R pair S i rho h

/--
[fkRectPrimalFullDistinctPairedWitness_insert_imp_adaptiveConnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean)
-/
@[path]
private lemma fkRectPrimalFullDistinctPairedWitness_insert_imp_adaptiveConnection_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {i : Fin R.height}
  {rho : ConfigSpace (Sym2 R.Vertex)}
-- given
  (pair : Fin R.height -> Fin R.height)
  (hi : i ∉ S)
  (h : FKRectPrimalFullDistinctPairedWitness R pair (insert i S) rho) :
-- imply
  rho ∈ FKRectPrimalAdaptivePairedConnectionEvent R S i (pair i) (fkRectPrimalAdaptiveProjection R S rho) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullDistinctPairedWitness_insert_imp_adaptiveConnection R pair S i hi rho h

/--
[fkRectPrimalFullDistinctPairedWitness_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean)
-/
@[path]
private lemma fkRectPrimalFullDistinctPairedWitness_step_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {i : Fin R.height}
  {p q : Real}
-- given
  (pair : Fin R.height -> Fin R.height)
  (hi : i ∉ S)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  StatMech.Probability.finiteEventMass (FK.fkProb (fkRectCutGraph R) p q) {rho | FKRectPrimalFullDistinctPairedWitness R pair (insert i S) rho} <= (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (FK.boxConnEvent 2 (R.width + R.height) (fkRectVertexBoxEmbedding R (fkRectLeftColumn R, i)) (fkRectVertexBoxEmbedding R (fkRectRightColumn R, pair i))) * StatMech.Probability.finiteEventMass (FK.fkProb (fkRectCutGraph R) p q) {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho} := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullDistinctPairedWitness_step R pair S i hi hp hp1 hq

/--
[fkRectPrimalPairedConnectionFactor_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean)
-/
@[path]
private lemma fkRectPrimalPairedConnectionFactor_nonneg_eq
  {R : FKRectTorus}
  {p q : Real}
  {i : Fin R.height}
-- given
  (pair : Fin R.height -> Fin R.height)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  0 <= fkRectPrimalPairedConnectionFactor R pair hp hp1 hq i := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalPairedConnectionFactor_nonneg R pair hp hp1 hq i

/--
[fkRectPrimalPairedConnectionFactor_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean)
-/
@[path]
private lemma fkRectPrimalPairedConnectionFactor_le_one_eq
  {R : FKRectTorus}
  {p q : Real}
  {i : Fin R.height}
-- given
  (pair : Fin R.height -> Fin R.height)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  fkRectPrimalPairedConnectionFactor R pair hp hp1 hq i <= 1 := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalPairedConnectionFactor_le_one R pair hp hp1 hq i

/--
[fkRectPrimalFullDistinctPairedWitness_mass_le_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean)
-/
@[path]
private lemma fkRectPrimalFullDistinctPairedWitness_mass_le_prod_eq
  {R : FKRectTorus}
  {p q : Real}
  {S : Finset (Fin R.height)}
-- given
  (pair : Fin R.height -> Fin R.height)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  StatMech.Probability.finiteEventMass (FK.fkProb (fkRectCutGraph R) p q) {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho} <= ∏ i ∈ S, fkRectPrimalPairedConnectionFactor R pair hp hp1 hq i := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullDistinctPairedWitness_mass_le_prod R pair hp hp1 hq S

/--
[fkRectPrimalFullDistinctPairedWitness_mass_le_prod_erase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean)
-/
@[path]
private lemma fkRectPrimalFullDistinctPairedWitness_mass_le_prod_erase_eq
  {R : FKRectTorus}
  {p q : Real}
  {S : Finset (Fin R.height)}
  {first : Fin R.height}
-- given
  (pair : Fin R.height -> Fin R.height)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hfirst : first ∈ S) :
-- imply
  StatMech.Probability.finiteEventMass (FK.fkProb (fkRectCutGraph R) p q) {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho} <= ∏ i ∈ S.erase first, fkRectPrimalPairedConnectionFactor R pair hp hp1 hq i := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullDistinctPairedWitness_mass_le_prod_erase R pair hp hp1 hq S first hfirst

/--
[fkRectPrimalFullDistinctPairedWitness_congr_openSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean)
-/
@[path]
private lemma fkRectPrimalFullDistinctPairedWitness_congr_openSub_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho sigma : ConfigSpace (Sym2 R.Vertex)}
-- given
  (pair : Fin R.height -> Fin R.height)
  (hgraph : FK.openSub (fkRectCutGraph R) rho = FK.openSub (fkRectCutGraph R) sigma) :
-- imply
  FKRectPrimalFullDistinctPairedWitness R pair S rho <-> FKRectPrimalFullDistinctPairedWitness R pair S sigma := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullDistinctPairedWitness_congr_openSub R pair S hgraph

/--
[fkRectPrimalStablePairedWitness_cutConfigOfFull_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean)
-/
@[path]
private lemma fkRectPrimalStablePairedWitness_cutConfigOfFull_iff_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho : ConfigSpace (Sym2 R.Vertex)}
-- given
  (pair : Fin R.height -> Fin R.height) :
-- imply
  FKRectPrimalStablePairedWitnessCore R pair S (fkRectCutConfigOfFull R rho).1 <-> FKRectPrimalFullDistinctPairedWitness R pair S rho := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalStablePairedWitness_cutConfigOfFull_iff R pair S rho

/--
[fkRectCutGraph_stablePairedWitnessEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean)
-/
@[path]
private lemma fkRectCutGraph_stablePairedWitnessEvent_eq_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
-- given
  (pair : Fin R.height -> Fin R.height) :
-- imply
  FK.ecz_closeOff (fkRectCutGraph R) ⁻¹' fkRectCutEdgeEvent R {eta | FKRectPrimalStablePairedWitnessCore R pair S eta} = {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho} := by
-- proof
  apply StatMech.FrontierD.fkRectCutGraph_stablePairedWitnessEvent_eq R pair S

/--
[fkRectCriticalCutFree_stablePairedWitness_eq_finiteEventMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean)
-/
@[path]
private lemma fkRectCriticalCutFree_stablePairedWitness_eq_finiteEventMass_eq
  {R : FKRectTorus}
  {q : Real}
  {S : Finset (Fin R.height)}
-- given
  (pair : Fin R.height -> Fin R.height)
  (hq : 1 <= q) :
-- imply
  fkRectCriticalCutFreeEventMass R q {eta | FKRectPrimalStablePairedWitnessCore R pair S eta} = StatMech.Probability.finiteEventMass (FK.fkProb (fkRectCutGraph R) (fkRectCriticalP q) q) {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho} := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalCutFree_stablePairedWitness_eq_finiteEventMass R pair hq S

/--
[fkRectCriticalCutFree_stablePairedWitness_le_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean)
-/
@[path]
private lemma fkRectCriticalCutFree_stablePairedWitness_le_prod_eq
  {R : FKRectTorus}
  {q : Real}
  {S : Finset (Fin R.height)}
-- given
  (pair : Fin R.height -> Fin R.height)
  (hq : 1 <= q) :
-- imply
  fkRectCriticalCutFreeEventMass R q {eta | FKRectPrimalStablePairedWitnessCore R pair S eta} <= ∏ i ∈ S, fkRectPrimalPairedConnectionFactor R pair (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq)) (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) hq i := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalCutFree_stablePairedWitness_le_prod R pair hq S


-- created on 2026-10-23
