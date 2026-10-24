import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.JordanWindingClose
open SimpleGraph Set StatMech StatMech.Lattice


/--
[jwc_faceAdj_NE_NW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_faceAdj_NE_NW_eq
  {c d : ℤ} :
-- imply
  (hypercubicLattice 2).Adj ![c, d] ![c - 1, d] := by
-- proof
  apply StatMech.Lattice.jwc_faceAdj_NE_NW c d

/--
[jwc_faceAdj_NW_SW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_faceAdj_NW_SW_eq
  {c d : ℤ} :
-- imply
  (hypercubicLattice 2).Adj ![c - 1, d] ![c - 1, d - 1] := by
-- proof
  apply StatMech.Lattice.jwc_faceAdj_NW_SW c d

/--
[jwc_faceAdj_SW_SE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_faceAdj_SW_SE_eq
  {c d : ℤ} :
-- imply
  (hypercubicLattice 2).Adj ![c - 1, d - 1] ![c, d - 1] := by
-- proof
  apply StatMech.Lattice.jwc_faceAdj_SW_SE c d

/--
[jwc_faceAdj_SE_NE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_faceAdj_SE_NE_eq
  {c d : ℤ} :
-- imply
  (hypercubicLattice 2).Adj ![c, d - 1] ![c, d] := by
-- proof
  apply StatMech.Lattice.jwc_faceAdj_SE_NE c d

/--
[jwc_shared_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_shared_eval_eq
  {f0 f1 g0 g1 : ℤ} :
-- imply
  sharedPrimalEdge ![f0, f1] ![g0, g1] = if f0 = g0 then s(![f0, max f1 g1], ![f0 + 1, max f1 g1]) else s(![max f0 g0, f1], ![max f0 g0, f1 + 1]) := by
-- proof
  apply StatMech.Lattice.jwc_shared_eval f0 f1 g0 g1

/--
[jwc_shared_NE_NW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_shared_NE_NW_eq
  {c d : ℤ} :
-- imply
  sharedPrimalEdge ![c, d] ![c - 1, d] = s(![c, d], ![c, d + 1]) := by
-- proof
  apply StatMech.Lattice.jwc_shared_NE_NW c d

/--
[jwc_shared_NW_SW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_shared_NW_SW_eq
  {c d : ℤ} :
-- imply
  sharedPrimalEdge ![c - 1, d] ![c - 1, d - 1] = s(![c - 1, d], ![c, d]) := by
-- proof
  apply StatMech.Lattice.jwc_shared_NW_SW c d

/--
[jwc_shared_SW_SE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_shared_SW_SE_eq
  {c d : ℤ} :
-- imply
  sharedPrimalEdge ![c - 1, d - 1] ![c, d - 1] = s(![c, d - 1], ![c, d]) := by
-- proof
  apply StatMech.Lattice.jwc_shared_SW_SE c d

/--
[jwc_shared_SE_NE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_shared_SE_NE_eq
  {c d : ℤ} :
-- imply
  sharedPrimalEdge ![c, d - 1] ![c, d] = s(![c, d], ![c + 1, d]) := by
-- proof
  apply StatMech.Lattice.jwc_shared_SE_NE c d

/--
[jwc_vertexLoop_flipCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_vertexLoop_flipCount_eq
  {E : Finset (Sym2 (Site 2))}
  {c d : ℤ} :
-- imply
  wcl_flipCount (jce_edgeFlip E) (jwc_vertexLoop c d) = (if s(![c, d], ![c, d + 1]) ∈ E then 1 else 0) + ((if s(![c - 1, d], ![c, d]) ∈ E then 1 else 0) + ((if s(![c, d - 1], ![c, d]) ∈ E then 1 else 0) + ((if s(![c, d], ![c + 1, d]) ∈ E then 1 else 0) + 0))) := by
-- proof
  apply StatMech.Lattice.jwc_vertexLoop_flipCount E c d

/--
[jwc_jce_degree_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_jce_degree_eq_eq
  {E : Finset (Sym2 (Site 2))}
  {c d : ℤ} :
-- imply
  jce_degree (E : Set (Sym2 (Site 2))) ![c, d] = (if s(![c, d], ![c, d + 1]) ∈ E then 1 else 0) + ((if s(![c - 1, d], ![c, d]) ∈ E then 1 else 0) + ((if s(![c, d - 1], ![c, d]) ∈ E then 1 else 0) + ((if s(![c, d], ![c + 1, d]) ∈ E then 1 else 0) + 0))) := by
-- proof
  apply StatMech.Lattice.jwc_jce_degree_eq E c d

/--
[jwc_vertexLoop_even_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_vertexLoop_even_iff_eq
  {E : Finset (Sym2 (Site 2))}
  {c d : ℤ} :
-- imply
  Even (wcl_flipCount (jce_edgeFlip E) (jwc_vertexLoop c d)) ↔ Even (jce_degree (E : Set (Sym2 (Site 2))) ![c, d]) := by
-- proof
  apply StatMech.Lattice.jwc_vertexLoop_even_iff E c d

/--
[jwc_closedContour_of_edgeFlip_closedEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_closedContour_of_edgeFlip_closedEven_eq
  {E : Finset (Sym2 (Site 2))}
-- given
  (hce : wcl_ClosedEven (jce_edgeFlip E)) :
-- imply
  jce_ClosedContour (E : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Lattice.jwc_closedContour_of_edgeFlip_closedEven E hce

/--
[jwc_edgeFlip_closedEven_iff_closedContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_edgeFlip_closedEven_iff_closedContour_eq
  {E : Finset (Sym2 (Site 2))} :
-- imply
  wcl_ClosedEven (jce_edgeFlip E) ↔ jce_ClosedContour (E : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Lattice.jwc_edgeFlip_closedEven_iff_closedContour E

/--
[jwc_cutFlip_closedEven_iff_closedContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_cutFlip_closedEven_iff_closedContour_eq
  {H : SimpleGraph (Site 2)}
  [Fintype H.edgeSet]
  {f0 g0 : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f0 g0) :
-- imply
  wcl_ClosedEven (wcl_cutFlip H f0 g0) ↔ jce_ClosedContour ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Lattice.jwc_cutFlip_closedEven_iff_closedContour H f0 g0 hfg

/--
[jwc_separated_of_closedContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_separated_of_closedContour_eq
  {H : SimpleGraph (Site 2)}
  [Fintype H.edgeSet]
  {f0 g0 : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hcc : jce_ClosedContour ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2)))) :
-- imply
  ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
-- proof
  apply StatMech.Lattice.jwc_separated_of_closedContour H f0 g0 hfg hcc

/--
[jwc_faithfulDiscreteJordan_of_evenPeelable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_faithfulDiscreteJordan_of_evenPeelable_eq
  {P : PlanarZ2Subgraph}
-- given
  (hpe : jcx_IsEvenPeelable P.G) :
-- imply
  whc_FaithfulDiscreteJordan P := by
-- proof
  apply StatMech.Lattice.jwc_faithfulDiscreteJordan_of_evenPeelable P hpe

/--
[jwc_faceRegion_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_faceRegion_antitone_eq
  {G1 G2 : SimpleGraph (Site 2)}
-- given
  (h : G1 ≤ G2) :
-- imply
  whb_faceRegion G2 ≤ whb_faceRegion G1 := by
-- proof
  apply StatMech.Lattice.jwc_faceRegion_antitone h

/--
[jwc_deleted_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_deleted_antitone_eq
  {G1 G2 : SimpleGraph (Site 2)}
  {f0 g0 : Site 2}
-- given
  (h : G1 ≤ G2) :
-- imply
  (whb_faceRegion G2).deleteEdges {s(f0, g0)} ≤ (whb_faceRegion G1).deleteEdges {s(f0, g0)} := by
-- proof
  apply StatMech.Lattice.jwc_deleted_antitone h f0 g0

/--
[jwc_separated_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_separated_mono_eq
  {G1 G2 : SimpleGraph (Site 2)}
  {f0 g0 : Site 2}
-- given
  (h : G1 ≤ G2)
  (hsep : ¬ ((whb_faceRegion G1).deleteEdges {s(f0, g0)}).Reachable f0 g0) :
-- imply
  ¬ ((whb_faceRegion G2).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
-- proof
  apply StatMech.Lattice.jwc_separated_mono h hsep

/--
[jwc_syncMerge_of_closedContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_syncMerge_of_closedContour_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {f0 g0 : Site 2}
-- given
  (hKle : K ≤ P.G)
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hcc : jce_ClosedContour ((insert (sharedPrimalEdge f0 g0) (jei_pushGraph_edgeSet_finite P K).toFinset : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2)))) :
-- imply
  ¬ ((whb_faceRegion (jei_pushGraph P K)).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
-- proof
  apply StatMech.Lattice.jwc_syncMerge_of_closedContour P K hKle hfg hcc

/--
[jwc_pushGraph_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_pushGraph_mono_eq
  {P : PlanarZ2Subgraph}
  {A B : SimpleGraph P.V}
-- given
  (h : A ≤ B) :
-- imply
  jei_pushGraph P A ≤ jei_pushGraph P B := by
-- proof
  apply StatMech.Lattice.jwc_pushGraph_mono P h

/--
[jwc_cyclePath_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_cyclePath_le_eq
  [DecidableEq V]
  {K : SimpleGraph V}
  {x y : V}
-- given
  (hreach : K.Reachable x y) :
-- imply
  jwc_cyclePath hreach ≤ K := by
-- proof
  apply StatMech.Lattice.jwc_cyclePath_le hreach

/--
[jwc_cyclePath_sup_edge_isEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_cyclePath_sup_edge_isEven_eq
  [Empty.Finite V]
  [DecidableEq V]
  {K : SimpleGraph V}
  {x y : V}
-- given
  (hreach : K.Reachable x y)
  (hne : x ≠ y)
  (hnadj : ¬ K.Adj x y) :
-- imply
  jcx_IsEven (jwc_cyclePath hreach ⊔ edge x y) := by
-- proof
  apply StatMech.Lattice.jwc_cyclePath_sup_edge_isEven hreach hne hnadj

/--
[jwc_syncMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_syncMerge_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {x y : P.V}
  {f0 g0 : Site 2}
-- given
  (hKle : K ≤ P.G)
  (hadjG : P.G.Adj x y)
  (hnotK : ¬ K.Adj x y)
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hshared : sharedPrimalEdge f0 g0 = s(P.emb x, P.emb y))
  (hreach : K.Reachable x y) :
-- imply
  ¬ ((whb_faceRegion (jei_pushGraph P K)).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
-- proof
  apply StatMech.Lattice.jwc_syncMerge P K hKle hadjG hnotK hfg hshared hreach

/--
[jwc_whbSync_of_keepResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_whbSync_of_keepResidue_eq
  {P : PlanarZ2Subgraph}
-- given
  (hkeep : jwc_KeepResidue P) :
-- imply
  jfc_WhbSync P := by
-- proof
  apply StatMech.Lattice.jwc_whbSync_of_keepResidue P hkeep

/--
[jwc_faithfulDiscreteJordan_of_keepResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_faithfulDiscreteJordan_of_keepResidue_eq
  {P : PlanarZ2Subgraph}
-- given
  (hkeep : jwc_KeepResidue P) :
-- imply
  whc_FaithfulDiscreteJordan P := by
-- proof
  apply StatMech.Lattice.jwc_faithfulDiscreteJordan_of_keepResidue P hkeep

/--
[jwc_square_edgeFlip_closedEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_square_edgeFlip_closedEven_eq :
-- imply
  wcl_ClosedEven (jce_edgeFlip (imageGraph jbc_Pce).edgeSet.toFinset) := by
-- proof
  apply StatMech.Lattice.jwc_square_edgeFlip_closedEven

/--
[jwc_square_vertexLoop_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_square_vertexLoop_even_eq
  {c d : ℤ} :
-- imply
  Even (wcl_flipCount (jce_edgeFlip (imageGraph jbc_Pce).edgeSet.toFinset) (jwc_vertexLoop c d)) := by
-- proof
  apply StatMech.Lattice.jwc_square_vertexLoop_even c d

/--
[jwc_keep_of_freeHead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_keep_of_freeHead_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {x y : P.V}
  {f0 g0 : Site 2}
-- given
  (hadjG : P.G.Adj x y)
  (hfree : ∀ w, ¬ (jei_pushGraph P K).Adj (P.emb x) w)
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hshared : sharedPrimalEdge f0 g0 = s(P.emb x, P.emb y)) :
-- imply
  ((whb_faceRegion (jei_pushGraph P K)).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
-- proof
  apply StatMech.Lattice.jwc_keep_of_freeHead P K hadjG hfree hfg hshared

/--
[jwc_summary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean)
-/
@[path]
private lemma jwc_summary_eq :
-- imply
  (∀ (H : SimpleGraph (Site 2)) [Fintype H.edgeSet] (f0 g0 : Site 2), (hypercubicLattice 2).Adj f0 g0 → (wcl_ClosedEven (wcl_cutFlip H f0 g0) ↔ jce_ClosedContour ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2))))) ∧ (∀ (P : PlanarZ2Subgraph), jwc_KeepResidue P → whc_FaithfulDiscreteJordan P) ∧ (∀ (P : PlanarZ2Subgraph), jcx_IsEvenPeelable P.G → whc_FaithfulDiscreteJordan P) := by
-- proof
  apply StatMech.Lattice.jwc_summary


-- created on 2026-10-23
