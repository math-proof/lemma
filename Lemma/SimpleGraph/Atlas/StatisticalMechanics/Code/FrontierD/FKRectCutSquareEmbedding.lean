import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
open MeasureTheory StatMech.Lattice SimpleGraph StatMech StatMech.FrontierD


/--
[freeBoxEvent_le_freeInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma freeBoxEvent_le_freeInfinite_eq
  {N : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 (FK.boxVerts 2 N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ omega, A.indicator (fun _ => (1 : Real)) omega * FK.fkProb (FK.boxGraph 2 N) p q omega) ≤ (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (FK.boxRestrict 2 N ⁻¹' A) := by
-- proof
  apply StatMech.FrontierD.freeBoxEvent_le_freeInfinite N hp hp1 hq hA

/--
[fkRectSquareSiteOfPair_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectSquareSiteOfPair_zero_eq
  {p : Int × Int} :
-- imply
  fkRectSquareSiteOfPair p 0 = p.1 := by
-- proof
  apply StatMech.FrontierD.fkRectSquareSiteOfPair_zero p

/--
[fkRectSquareSiteOfPair_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectSquareSiteOfPair_one_eq
  {p : Int × Int} :
-- imply
  fkRectSquareSiteOfPair p 1 = p.2 := by
-- proof
  apply StatMech.FrontierD.fkRectSquareSiteOfPair_one p

/--
[fkRectSquareSiteOfPair_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectSquareSiteOfPair_injective_eq :
-- imply
  Function.Injective fkRectSquareSiteOfPair := by
-- proof
  apply StatMech.FrontierD.fkRectSquareSiteOfPair_injective

/--
[fkRectVertexSquareSite_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectVertexSquareSite_injective_eq
  {R : FKRectTorus} :
-- imply
  Function.Injective (fkRectVertexSquareSite R) := by
-- proof
  apply StatMech.FrontierD.fkRectVertexSquareSite_injective R

/--
[fkRectSquareAxisStep_iff_hypercubicAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectSquareAxisStep_iff_hypercubicAdj_eq
  {p q : Int × Int} :
-- imply
  FKRectSquareAxisStep p q ↔ (hypercubicLattice 2).Adj (fkRectSquareSiteOfPair p) (fkRectSquareSiteOfPair q) := by
-- proof
  apply StatMech.FrontierD.fkRectSquareAxisStep_iff_hypercubicAdj p q

/--
[mem_fkRectHorizontalCutEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma mem_fkRectHorizontalCutEdges_iff_eq
  {R : FKRectTorus}
  {a : R.EdgeIndex} :
-- imply
  a ∈ fkRectHorizontalCutEdges R ↔ a.2.2.val = 0 := by
-- proof
  apply StatMech.FrontierD.mem_fkRectHorizontalCutEdges_iff R a

/--
[mem_fkRectVerticalCutEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma mem_fkRectVerticalCutEdges_iff_eq
  {R : FKRectTorus}
  {a : R.EdgeIndex} :
-- imply
  a ∈ fkRectVerticalCutEdges R ↔ a.1 = false ∧ a.2.1.val = 0 := by
-- proof
  apply StatMech.FrontierD.mem_fkRectVerticalCutEdges_iff R a

/--
[mem_fkRectTorusCutEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma mem_fkRectTorusCutEdges_iff_eq
  {R : FKRectTorus}
  {a : R.EdgeIndex} :
-- imply
  a ∈ fkRectTorusCutEdges R ↔ a.2.2.val = 0 ∨ (a.1 = false ∧ a.2.1.val = 0) := by
-- proof
  apply StatMech.FrontierD.mem_fkRectTorusCutEdges_iff R a

/--
[fkRectLiftedIndexedEdgeEnds_develop_eq_vertexPoint_of_not_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectLiftedIndexedEdgeEnds_develop_eq_vertexPoint_of_not_cut_eq
  {R : FKRectTorus}
  {a : R.EdgeIndex}
-- given
  (ha : a ∉ fkRectTorusCutEdges R) :
-- imply
  fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R a).1 = fkRectVertexSquarePoint R (fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R a).1) := by
-- proof
  apply StatMech.FrontierD.fkRectLiftedIndexedEdgeEnds_develop_eq_vertexPoint_of_not_cut R a ha

/--
[fkRectLiftedIndexedEdgeEnds_develop_eq_vertexPoint_of_not_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectLiftedIndexedEdgeEnds_develop_eq_vertexPoint_of_not_cut_eq_2
  {R : FKRectTorus}
  {a : R.EdgeIndex}
-- given
  (ha : a ∉ fkRectTorusCutEdges R) :
-- imply
  fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R a).2 = fkRectVertexSquarePoint R (fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R a).2) := by
-- proof
  apply StatMech.FrontierD.fkRectLiftedIndexedEdgeEnds_develop_eq_vertexPoint_of_not_cut R a ha

/--
[fkRectCutGraph_adj_imp_hypercubicAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectCutGraph_adj_imp_hypercubicAdj_eq
  {R : FKRectTorus}
  {x y : R.Vertex}
-- given
  (hxy : (fkRectCutGraph R).Adj x y) :
-- imply
  (hypercubicLattice 2).Adj (fkRectVertexSquareSite R x) (fkRectVertexSquareSite R y) := by
-- proof
  apply StatMech.FrontierD.fkRectCutGraph_adj_imp_hypercubicAdj R hxy

/--
[fkRectCutGraph_adj_iff_hypercubicAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectCutGraph_adj_iff_hypercubicAdj_eq
  {R : FKRectTorus}
  {x y : R.Vertex} :
-- imply
  (fkRectCutGraph R).Adj x y ↔ (hypercubicLattice 2).Adj (fkRectVertexSquareSite R x) (fkRectVertexSquareSite R y) := by
-- proof
  apply StatMech.FrontierD.fkRectCutGraph_adj_iff_hypercubicAdj R x y

/--
[fkRectVertexSquareSite_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectVertexSquareSite_mem_box_eq
  {R : FKRectTorus}
  {x : R.Vertex} :
-- imply
  fkRectVertexSquareSite R x ∈ box 2 (R.width + R.height) := by
-- proof
  apply StatMech.FrontierD.fkRectVertexSquareSite_mem_box R x

/--
[fkRectVertexBoxEmbedding_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectVertexBoxEmbedding_injective_eq
  {R : FKRectTorus} :
-- imply
  Function.Injective (fkRectVertexBoxEmbedding R) := by
-- proof
  apply StatMech.FrontierD.fkRectVertexBoxEmbedding_injective R

/--
[fkRectCutGraph_boxAdjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectCutGraph_boxAdjMatch_eq
  {R : FKRectTorus} :
-- imply
  FK.ocd_AdjMatch (fkRectCutGraph R) (FK.boxGraph 2 (R.width + R.height)) (fkRectVertexBoxEmbedding R) := by
-- proof
  apply StatMech.FrontierD.fkRectCutGraph_boxAdjMatch R

/--
[fkRectPrimalUnexploredBoxEmbedding_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectPrimalUnexploredBoxEmbedding_injective_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration} :
-- imply
  Function.Injective (fkRectPrimalUnexploredBoxEmbedding R S eta) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalUnexploredBoxEmbedding_injective R S eta

/--
[fkRectPrimalUnexplored_boxAdjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectPrimalUnexplored_boxAdjMatch_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration} :
-- imply
  FK.ocd_AdjMatch (fkRectPrimalUnexploredInducedGraph R S eta) (FK.boxGraph 2 (R.width + R.height)) (fkRectPrimalUnexploredBoxEmbedding R S eta) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalUnexplored_boxAdjMatch R S eta

/--
[fkRectPrimalUnexplored_freeEvent_le_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectPrimalUnexplored_freeEvent_le_box_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 (FKRectPrimalUnexploredVertex R S eta)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ omega, A.indicator (fun _ => (1 : Real)) omega * FK.fkProb (fkRectPrimalUnexploredInducedGraph R S eta) p q omega) ≤ ∑ rho, (FK.ocd_innerRestrict (fkRectPrimalUnexploredBoxEmbedding R S eta) ⁻¹' A).indicator (fun _ => (1 : Real)) rho * FK.fkProb (FK.boxGraph 2 (R.width + R.height)) p q rho := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalUnexplored_freeEvent_le_box R S eta hp hp1 hq hA

/--
[fkRectPrimalUnexplored_freeEvent_le_freeInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectPrimalUnexplored_freeEvent_le_freeInfinite_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 (FKRectPrimalUnexploredVertex R S eta)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ omega, A.indicator (fun _ => (1 : Real)) omega * FK.fkProb (fkRectPrimalUnexploredInducedGraph R S eta) p q omega) ≤ (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (FK.boxRestrict 2 (R.width + R.height) ⁻¹' (FK.ocd_innerRestrict (fkRectPrimalUnexploredBoxEmbedding R S eta) ⁻¹' A)) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalUnexplored_freeEvent_le_freeInfinite R S eta hp hp1 hq hA

/--
[fkRectPrimalUnexploredRightArmEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectPrimalUnexploredRightArmEvent_isIncreasing_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration}
  {source : FKRectPrimalUnexploredVertex R S eta} :
-- imply
  IsIncreasing (FKRectPrimalUnexploredRightArmEvent R S eta source) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalUnexploredRightArmEvent_isIncreasing R S eta source

/--
[fkRectPrimalUnexplored_reachable_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectPrimalUnexplored_reachable_box_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration}
  {rho : ConfigSpace (Sym2 (FK.boxVerts 2 (R.width + R.height)))}
  {x y : FKRectPrimalUnexploredVertex R S eta}
-- given
  (hreach : (FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta) (FK.ocd_innerRestrict (fkRectPrimalUnexploredBoxEmbedding R S eta) rho)).Reachable x y) :
-- imply
  (FK.openSub (FK.boxGraph 2 (R.width + R.height)) rho).Reachable (fkRectPrimalUnexploredBoxEmbedding R S eta x) (fkRectPrimalUnexploredBoxEmbedding R S eta y) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalUnexplored_reachable_box R S eta rho hreach

/--
[fkRectPrimalUnexplored_rightArmCylinder_subset_boxConnections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectPrimalUnexplored_rightArmCylinder_subset_boxConnections_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration}
  {source : FKRectPrimalUnexploredVertex R S eta} :
-- imply
  FK.boxRestrict 2 (R.width + R.height) ⁻¹' (FK.ocd_innerRestrict (fkRectPrimalUnexploredBoxEmbedding R S eta) ⁻¹' FKRectPrimalUnexploredRightArmEvent R S eta source) ⊆ ⋃ target : FKRectPrimalUnexploredVertex R S eta, ⋃ _ : target.1.1 = fkRectRightColumn R, FK.boxConnEvent 2 (R.width + R.height) (fkRectPrimalUnexploredBoxEmbedding R S eta source) (fkRectPrimalUnexploredBoxEmbedding R S eta target) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalUnexplored_rightArmCylinder_subset_boxConnections R S eta source

/--
[fkRectLeftRightSquareDisplacement_not_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectLeftRightSquareDisplacement_not_mem_box_eq
  {R : FKRectTorus}
  {i z : Fin R.height} :
-- imply
  -fkRectVertexSquareSite R (fkRectLeftColumn R, i) + fkRectVertexSquareSite R (fkRectRightColumn R, z) ∉ box 2 (R.width - 2) := by
-- proof
  apply StatMech.FrontierD.fkRectLeftRightSquareDisplacement_not_mem_box R i z

/--
[fkRectBox_reachable_global](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectBox_reachable_global_eq
  {N : Nat}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x y : FK.boxVerts 2 N}
-- given
  (hreach : (FK.openSub (FK.boxGraph 2 N) (FK.boxRestrict 2 N omega)).Reachable x y) :
-- imply
  Connected 2 omega x.1 y.1 := by
-- proof
  apply StatMech.FrontierD.fkRectBox_reachable_global N omega hreach

/--
[fkRectPrimalUnexplored_rightArmCylinder_subset_shift_boxBdry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectPrimalUnexplored_rightArmCylinder_subset_shift_boxBdry_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.height)}
  {eta : R.Configuration}
  {source : FKRectPrimalUnexploredVertex R S eta}
-- given
  (hleft : source.1.1 = fkRectLeftColumn R) :
-- imply
  let sourceSite := (fkRectPrimalUnexploredBoxEmbedding R S eta source).1 let g : Multiplicative (Site 2) := Multiplicative.ofAdd (-sourceSite) FK.boxRestrict 2 (R.width + R.height) ⁻¹' (FK.ocd_innerRestrict (fkRectPrimalUnexploredBoxEmbedding R S eta) ⁻¹' FKRectPrimalUnexploredRightArmEvent R S eta source) ⊆ (ConfigSpace.shift g) ⁻¹' FK.boxBdryConnEvent 2 (R.width - 2) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalUnexplored_rightArmCylinder_subset_shift_boxBdry R S eta source hleft

/--
[fkRectPrimalUnexploredRightArm_freeMass_le_boxBdry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean)
-/
@[path]
private lemma fkRectPrimalUnexploredRightArm_freeMass_le_boxBdry_eq
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
  (∑ omega, (FKRectPrimalUnexploredRightArmEvent R S eta source).indicator (fun _ => (1 : Real)) omega * FK.fkProb (fkRectPrimalUnexploredInducedGraph R S eta) p q omega) ≤ (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (FK.boxBdryConnEvent 2 (R.width - 2)) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalUnexploredRightArm_freeMass_le_boxBdry R S eta source hleft hp hp1 hq


-- created on 2026-10-23
