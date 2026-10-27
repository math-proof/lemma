import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part9
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectFullGraphConfiguration_cutConfigOfFull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectFullGraphConfiguration_cutConfigOfFull_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)} :
-- imply
  fkRectFullGraphConfiguration R (fkRectCutConfigOfFull R rho).1 = (FK.ecz_closeOff (fkRectCutGraph R) rho).1 := by
-- proof
  apply StatMech.FrontierD.fkRectFullGraphConfiguration_cutConfigOfFull R rho

/--
[fkRectOpenGraph_cutConfigOfFull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectOpenGraph_cutConfigOfFull_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)} :
-- imply
  fkRectOpenGraph R (fkRectCutConfigOfFull R rho).1 = FK.openSub (fkRectCutGraph R) rho := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_cutConfigOfFull R rho

/--
[fkRectPrimalFullExploredVertex_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalFullExploredVertex_iff_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {v : R.Vertex} :
-- imply
  FKRectPrimalFullExploredVertex R S rho v ↔ FKRectPrimalExploredVertex R S (fkRectCutConfigOfFull R rho).1 v := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullExploredVertex_iff R S rho v

/--
[mem_fkRectPrimalUnexploredPairEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma mem_fkRectPrimalUnexploredPairEdges_iff_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration}
  {e : Sym2 R.Vertex} :
-- imply
  e ∈ fkRectPrimalUnexploredPairEdges R S eta ↔ ∃ x y : R.Vertex, e = s(x, y) ∧ ¬ FKRectPrimalExploredVertex R S eta x ∧ ¬ FKRectPrimalExploredVertex R S eta y := by
-- proof
  apply StatMech.FrontierD.mem_fkRectPrimalUnexploredPairEdges_iff R S eta e

/--
[mem_fkRectPrimalFullUnexploredPairEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma mem_fkRectPrimalFullUnexploredPairEdges_iff_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {e : Sym2 R.Vertex} :
-- imply
  e ∈ fkRectPrimalFullUnexploredPairEdges R S rho ↔ ∃ x y : R.Vertex, e = s(x, y) ∧ ¬ FKRectPrimalFullExploredVertex R S rho x ∧ ¬ FKRectPrimalFullExploredVertex R S rho y := by
-- proof
  apply StatMech.FrontierD.mem_fkRectPrimalFullUnexploredPairEdges_iff R S rho e

/--
[fkRectPrimalFullUnexploredPairEdges_eq_decoded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalFullUnexploredPairEdges_eq_decoded_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho : ConfigSpace (Sym2 R.Vertex)} :
-- imply
  fkRectPrimalFullUnexploredPairEdges R S rho = fkRectPrimalUnexploredPairEdges R S (fkRectCutConfigOfFull R rho).1 := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullUnexploredPairEdges_eq_decoded R S rho

/--
[fkRectPrimalAdaptiveProjection_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalAdaptiveProjection_le_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho : ConfigSpace (Sym2 R.Vertex)} :
-- imply
  fkRectPrimalAdaptiveProjection R S rho ≤ rho := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalAdaptiveProjection_le R S rho

/--
[fkRectPrimalAdaptiveProjection_eq_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalAdaptiveProjection_eq_of_not_mem_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {e : Sym2 R.Vertex}
-- given
  (he : e ∉ fkRectPrimalAdaptiveInsideEdges R S rho) :
-- imply
  fkRectPrimalAdaptiveProjection R S rho e = rho e := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalAdaptiveProjection_eq_of_not_mem R S rho he

/--
[not_mem_fkRectPrimalFullUnexploredPairEdges_of_explored_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma not_mem_fkRectPrimalFullUnexploredPairEdges_of_explored_left_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {x y : R.Vertex}
-- given
  (hx : FKRectPrimalFullExploredVertex R S rho x) :
-- imply
  s(x, y) ∉ fkRectPrimalFullUnexploredPairEdges R S rho := by
-- proof
  apply StatMech.FrontierD.not_mem_fkRectPrimalFullUnexploredPairEdges_of_explored_left R S rho hx

/--
[fkRectPrimalAdaptiveProjection_openAdj_of_explored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalAdaptiveProjection_openAdj_of_explored_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {x y : R.Vertex}
-- given
  (hx : FKRectPrimalFullExploredVertex R S rho x)
  (hxy : (FK.openSub (fkRectCutGraph R) rho).Adj x y) :
-- imply
  (FK.openSub (fkRectCutGraph R) (fkRectPrimalAdaptiveProjection R S rho)).Adj x y := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalAdaptiveProjection_openAdj_of_explored R S rho hx hxy

/--
[fkRectPrimalFullExploredVertex_projection_of_explored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalFullExploredVertex_projection_of_explored_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {v : R.Vertex}
-- given
  (hv : FKRectPrimalFullExploredVertex R S rho v) :
-- imply
  FKRectPrimalFullExploredVertex R S (fkRectPrimalAdaptiveProjection R S rho) v := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullExploredVertex_projection_of_explored R S rho hv

/--
[fkRectPrimalFullExploredVertex_of_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalFullExploredVertex_of_projection_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {v : R.Vertex}
-- given
  (hv : FKRectPrimalFullExploredVertex R S (fkRectPrimalAdaptiveProjection R S rho) v) :
-- imply
  FKRectPrimalFullExploredVertex R S rho v := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullExploredVertex_of_projection R S rho hv

/--
[fkRectPrimalFullExploredVertex_projection_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalFullExploredVertex_projection_iff_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {v : R.Vertex} :
-- imply
  FKRectPrimalFullExploredVertex R S (fkRectPrimalAdaptiveProjection R S rho) v ↔ FKRectPrimalFullExploredVertex R S rho v := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullExploredVertex_projection_iff R S rho v

/--
[fkRectPrimalAdaptiveInsideEdges_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalAdaptiveInsideEdges_projection_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho : ConfigSpace (Sym2 R.Vertex)} :
-- imply
  fkRectPrimalAdaptiveInsideEdges R S (fkRectPrimalAdaptiveProjection R S rho) = fkRectPrimalAdaptiveInsideEdges R S rho := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalAdaptiveInsideEdges_projection R S rho

/--
[fkRectPrimalAdaptiveProjection_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalAdaptiveProjection_idem_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho : ConfigSpace (Sym2 R.Vertex)} :
-- imply
  fkRectPrimalAdaptiveProjection R S (fkRectPrimalAdaptiveProjection R S rho) = fkRectPrimalAdaptiveProjection R S rho := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalAdaptiveProjection_idem R S rho

/--
[fkRectPrimalSourceReachable_projection_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalSourceReachable_projection_iff_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {i : Fin R.height}
  {v : R.Vertex}
-- given
  (hi : i ∈ S) :
-- imply
  (FK.openSub (fkRectCutGraph R) (fkRectPrimalAdaptiveProjection R S rho)).Reachable (fkRectLeftColumn R, i) v ↔ (FK.openSub (fkRectCutGraph R) rho).Reachable (fkRectLeftColumn R, i) v := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalSourceReachable_projection_iff R S rho hi v

/--
[fkRectPrimalFullDistinctCrossingWitness_projection_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalFullDistinctCrossingWitness_projection_iff_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho : ConfigSpace (Sym2 R.Vertex)} :
-- imply
  FKRectPrimalFullDistinctCrossingWitness R S (fkRectPrimalAdaptiveProjection R S rho) ↔ FKRectPrimalFullDistinctCrossingWitness R S rho := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullDistinctCrossingWitness_projection_iff R S rho

/--
[fkRectPrimalFullDistinctCrossingWitness_fibre_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalFullDistinctCrossingWitness_fibre_iff_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho sigma : ConfigSpace (Sym2 R.Vertex)}
-- given
  (hproj : fkRectPrimalAdaptiveProjection R S rho = fkRectPrimalAdaptiveProjection R S sigma) :
-- imply
  FKRectPrimalFullDistinctCrossingWitness R S rho ↔ FKRectPrimalFullDistinctCrossingWitness R S sigma := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullDistinctCrossingWitness_fibre_iff R S hproj

/--
[fkRectPrimalSourceReachable_agreesOff_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalSourceReachable_agreesOff_iff_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {psi rho : ConfigSpace (Sym2 R.Vertex)}
  {i : Fin R.height}
  {v : R.Vertex}
-- given
  (hagree : FK.AgreesOff (fkRectPrimalAdaptiveInsideEdges R S psi) psi rho)
  (hi : i ∈ S) :
-- imply
  (FK.openSub (fkRectCutGraph R) psi).Reachable (fkRectLeftColumn R, i) v ↔ (FK.openSub (fkRectCutGraph R) rho).Reachable (fkRectLeftColumn R, i) v := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalSourceReachable_agreesOff_iff R S psi rho hagree hi v

/--
[fkRectPrimalFullExploredVertex_agreesOff_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalFullExploredVertex_agreesOff_iff_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {psi rho : ConfigSpace (Sym2 R.Vertex)}
  {v : R.Vertex}
-- given
  (hagree : FK.AgreesOff (fkRectPrimalAdaptiveInsideEdges R S psi) psi rho) :
-- imply
  FKRectPrimalFullExploredVertex R S psi v ↔ FKRectPrimalFullExploredVertex R S rho v := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullExploredVertex_agreesOff_iff R S psi rho hagree v

/--
[fkRectPrimalAdaptiveInsideEdges_eq_of_agreesOff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalAdaptiveInsideEdges_eq_of_agreesOff_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {psi rho : ConfigSpace (Sym2 R.Vertex)}
-- given
  (hagree : FK.AgreesOff (fkRectPrimalAdaptiveInsideEdges R S psi) psi rho) :
-- imply
  fkRectPrimalAdaptiveInsideEdges R S rho = fkRectPrimalAdaptiveInsideEdges R S psi := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalAdaptiveInsideEdges_eq_of_agreesOff R S psi rho hagree

/--
[fkRectPrimalAdaptiveProjection_filter_eq_condFibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalAdaptiveProjection_filter_eq_condFibre_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {psi : ConfigSpace (Sym2 R.Vertex)}
-- given
  (hpsi : fkRectPrimalAdaptiveProjection R S psi = psi) :
-- imply
  Finset.univ.filter (fun rho => fkRectPrimalAdaptiveProjection R S rho = psi) = FK.condFibre (fkRectPrimalAdaptiveInsideEdges R S psi) psi := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalAdaptiveProjection_filter_eq_condFibre R S psi hpsi

/--
[fkRectPrimalFullDistinctCrossingWitness_insert_not_explored_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalFullDistinctCrossingWitness_insert_not_explored_of_reachable_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {i : Fin R.height}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {v : R.Vertex}
-- given
  (hi : i ∉ S)
  (h : FKRectPrimalFullDistinctCrossingWitness R (insert i S) rho)
  (hiv : (FK.openSub (fkRectCutGraph R) rho).Reachable (fkRectLeftColumn R, i) v) :
-- imply
  ¬ FKRectPrimalFullExploredVertex R S rho v := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullDistinctCrossingWitness_insert_not_explored_of_reachable R S i hi rho h hiv

/--
[fkRectPrimalFullDistinctCrossingWitness_insert_imp_adaptiveArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalFullDistinctCrossingWitness_insert_imp_adaptiveArm_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {i : Fin R.height}
  {rho : ConfigSpace (Sym2 R.Vertex)}
-- given
  (hi : i ∉ S)
  (h : FKRectPrimalFullDistinctCrossingWitness R (insert i S) rho) :
-- imply
  rho ∈ FKRectPrimalAdaptiveArmEvent R S i (fkRectPrimalAdaptiveProjection R S rho) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullDistinctCrossingWitness_insert_imp_adaptiveArm R S i hi rho h

/--
[fkRectPrimalFullDistinctCrossingWitness_insert_imp_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalFullDistinctCrossingWitness_insert_imp_base_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {i : Fin R.height}
  {rho : ConfigSpace (Sym2 R.Vertex)}
-- given
  (h : FKRectPrimalFullDistinctCrossingWitness R (insert i S) rho) :
-- imply
  FKRectPrimalFullDistinctCrossingWitness R S rho := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullDistinctCrossingWitness_insert_imp_base R S i rho h

/--
[fkRectPrimalFullDistinctCrossingWitness_insert_source_not_explored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalFullDistinctCrossingWitness_insert_source_not_explored_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {i : Fin R.height}
  {rho : ConfigSpace (Sym2 R.Vertex)}
-- given
  (hi : i ∉ S)
  (h : FKRectPrimalFullDistinctCrossingWitness R (insert i S) rho) :
-- imply
  ¬ FKRectPrimalFullExploredVertex R S rho (fkRectLeftColumn R, i) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullDistinctCrossingWitness_insert_source_not_explored R S i hi rho h

/--
[fkRectPrimalAdaptive_condRightArm_le_boxBdry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalAdaptive_condRightArm_le_boxBdry_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {psi : ConfigSpace (Sym2 R.Vertex)}
  {source : FKRectPrimalUnexploredVertex R S (fkRectCutConfigOfFull R psi).1}
  {p q : Real}
-- given
  (hleft : source.1.1 = fkRectLeftColumn R)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (∑ rho : ConfigSpace (Sym2 R.Vertex), (FK.ocd_innerRestrict (Subtype.val : FKRectPrimalUnexploredVertex R S (fkRectCutConfigOfFull R psi).1 → R.Vertex) ⁻¹' FKRectPrimalUnexploredRightArmEvent R S (fkRectCutConfigOfFull R psi).1 source).indicator (fun _ => (1 : Real)) rho * FK.condBcProb (fkRectCutGraph R) (StatMech.Lattice.boundaryCliqueGraph (fun _ : R.Vertex => False)) p q (fkRectPrimalFullUnexploredPairEdges R S psi) psi rho) ≤ (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (FK.boxBdryConnEvent 2 (R.width - 2)) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalAdaptive_condRightArm_le_boxBdry R S psi source hleft hp hp1 hq

/--
[fkRectPrimalAdaptiveArmEvent_condMass_le_boxBdry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalAdaptiveArmEvent_condMass_le_boxBdry_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {i : Fin R.height}
  {psi : ConfigSpace (Sym2 R.Vertex)}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (∑ rho : ConfigSpace (Sym2 R.Vertex), (FKRectPrimalAdaptiveArmEvent R S i psi).indicator (fun _ => (1 : Real)) rho * FK.condBcProb (fkRectCutGraph R) (StatMech.Lattice.boundaryCliqueGraph (fun _ : R.Vertex => False)) p q (fkRectPrimalAdaptiveInsideEdges R S psi) psi rho) ≤ (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (FK.boxBdryConnEvent 2 (R.width - 2)) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalAdaptiveArmEvent_condMass_le_boxBdry R S i psi hp hp1 hq

/--
[fkRectPrimalFullDistinctCrossingWitness_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalFullDistinctCrossingWitness_step_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {i : Fin R.height}
  {p q : Real}
-- given
  (hi : i ∉ S)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  StatMech.Probability.finiteEventMass (FK.fkProb (fkRectCutGraph R) p q) {rho | FKRectPrimalFullDistinctCrossingWitness R (insert i S) rho} ≤ (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (FK.boxBdryConnEvent 2 (R.width - 2)) * StatMech.Probability.finiteEventMass (FK.fkProb (fkRectCutGraph R) p q) {rho | FKRectPrimalFullDistinctCrossingWitness R S rho} := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullDistinctCrossingWitness_step R S i hi hp hp1 hq

/--
[fkRectPrimalFullDistinctCrossingWitness_congr_openSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalFullDistinctCrossingWitness_congr_openSub_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho sigma : ConfigSpace (Sym2 R.Vertex)}
-- given
  (hgraph : FK.openSub (fkRectCutGraph R) rho = FK.openSub (fkRectCutGraph R) sigma) :
-- imply
  FKRectPrimalFullDistinctCrossingWitness R S rho ↔ FKRectPrimalFullDistinctCrossingWitness R S sigma := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullDistinctCrossingWitness_congr_openSub R S hgraph

/--
[fkRectPrimalStableCrossingWitness_cutConfigOfFull_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalStableCrossingWitness_cutConfigOfFull_iff_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {rho : ConfigSpace (Sym2 R.Vertex)} :
-- imply
  FKRectPrimalStableCrossingWitnessCore R S (fkRectCutConfigOfFull R rho).1 ↔ FKRectPrimalFullDistinctCrossingWitness R S rho := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalStableCrossingWitness_cutConfigOfFull_iff R S rho

/--
[fkRectCutGraph_stableWitnessEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectCutGraph_stableWitnessEvent_eq_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)} :
-- imply
  FK.ecz_closeOff (fkRectCutGraph R) ⁻¹' fkRectCutEdgeEvent R {eta | FKRectPrimalStableCrossingWitnessCore R S eta} = {rho | FKRectPrimalFullDistinctCrossingWitness R S rho} := by
-- proof
  apply StatMech.FrontierD.fkRectCutGraph_stableWitnessEvent_eq R S

/--
[fkRectCriticalCutFree_stableWitness_eq_finiteEventMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectCriticalCutFree_stableWitness_eq_finiteEventMass_eq
  {R : FKRectTorus}
  {q : Real}
  {S : Finset (Fin R.height)}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkRectCriticalCutFreeEventMass R q {eta | FKRectPrimalStableCrossingWitnessCore R S eta} = StatMech.Probability.finiteEventMass (FK.fkProb (fkRectCutGraph R) (fkRectCriticalP q) q) {rho | FKRectPrimalFullDistinctCrossingWitness R S rho} := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalCutFree_stableWitness_eq_finiteEventMass R hq S

/--
[fkRectCriticalCutFree_stableWitness_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectCriticalCutFree_stableWitness_step_eq
  {R : FKRectTorus}
  {q : Real}
  {S : Finset (Fin R.height)}
  {i : Fin R.height}
-- given
  (hq : 1 ≤ q)
  (hi : i ∉ S) :
-- imply
  fkRectCriticalCutFreeEventMass R q {eta | FKRectPrimalStableCrossingWitnessCore R (insert i S) eta} ≤ (FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq)) (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) (zero_lt_one.trans_le hq) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (FK.boxBdryConnEvent 2 (R.width - 2)) * fkRectCriticalCutFreeEventMass R q {eta | FKRectPrimalStableCrossingWitnessCore R S eta} := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalCutFree_stableWitness_step R hq S i hi

/--
[fkRectPrimalFullDistinctCrossingWitness_mass_le_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalFullDistinctCrossingWitness_mass_le_pow_eq
  {R : FKRectTorus}
  {p q : Real}
  {S : Finset (Fin R.height)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  StatMech.Probability.finiteEventMass (FK.fkProb (fkRectCutGraph R) p q) {rho | FKRectPrimalFullDistinctCrossingWitness R S rho} ≤ ((FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (FK.boxBdryConnEvent 2 (R.width - 2))) ^ S.card := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullDistinctCrossingWitness_mass_le_pow R hp hp1 hq S

/--
[fkRectPrimalFullCrossingClusterCount_le_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalFullCrossingClusterCount_le_height_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)} :
-- imply
  fkRectPrimalFullCrossingClusterCount R rho ≤ R.height := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullCrossingClusterCount_le_height R rho

/--
[exists_fkRectPrimalFullDistinctCrossingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma exists_fkRectPrimalFullDistinctCrossingWitness_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {n : Nat}
-- given
  (hn : n ≤ fkRectPrimalFullCrossingClusterCount R rho) :
-- imply
  ∃ S : Finset (Fin R.height), S.card = n ∧ FKRectPrimalFullDistinctCrossingWitness R S rho := by
-- proof
  apply StatMech.FrontierD.exists_fkRectPrimalFullDistinctCrossingWitness R rho n hn

/--
[fkRectPrimalFullCrossingTail_le_choose_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectPrimalFullCrossingTail_le_choose_mul_pow_eq
  {R : FKRectTorus}
  {p q : Real}
  {n : Nat}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  StatMech.Probability.finiteEventMass (FK.fkProb (fkRectCutGraph R) p q) {rho | n < fkRectPrimalFullCrossingClusterCount R rho} ≤ Nat.choose R.height (n + 1) * ((FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalFullCrossingTail_le_choose_mul_pow R hp hp1 hq n

/--
[fkRectCutGraph_primalCrossingTailEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectCutGraph_primalCrossingTailEvent_eq_eq
  {R : FKRectTorus}
  {n : Nat} :
-- imply
  FK.ecz_closeOff (fkRectCutGraph R) ⁻¹' fkRectCutEdgeEvent R {eta | n < fkRectRawHorizontalCrossingClusterCount R (fkRectForceCutClosed R eta)} = {rho | n < fkRectPrimalFullCrossingClusterCount R rho} := by
-- proof
  apply StatMech.FrontierD.fkRectCutGraph_primalCrossingTailEvent_eq R n

/--
[fkRectCriticalCutFree_primalCrossingTail_eq_finiteEventMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectCriticalCutFree_primalCrossingTail_eq_finiteEventMass_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkRectCriticalCutFreeEventMass R q {eta | n < fkRectRawHorizontalCrossingClusterCount R (fkRectForceCutClosed R eta)} = StatMech.Probability.finiteEventMass (FK.fkProb (fkRectCutGraph R) (fkRectCriticalP q) q) {rho | n < fkRectPrimalFullCrossingClusterCount R rho} := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalCutFree_primalCrossingTail_eq_finiteEventMass R hq n

/--
[fkRectCriticalCutFree_primalCrossingTail_le_choose_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectCriticalCutFree_primalCrossingTail_le_choose_mul_pow_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkRectCriticalCutFreeEventMass R q {eta | n < fkRectRawHorizontalCrossingClusterCount R (fkRectForceCutClosed R eta)} ≤ Nat.choose R.height (n + 1) * ((FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq)) (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) (zero_lt_one.trans_le hq) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalCutFree_primalCrossingTail_le_choose_mul_pow R hq n


-- created on 2026-10-23
