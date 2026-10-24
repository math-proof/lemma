import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.KWGeometricDual
open Finset SimpleGraph Set StatMech StatMech.Ising


/--
[kwg_mem_allEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_mem_allEdges_eq
  {P : PlanarZ2Subgraph}
  {e : kwg_Edge P} :
-- imply
  e ∈ kwg_allEdges P := by
-- proof
  apply StatMech.Ising.kwg_mem_allEdges P e

/--
[kwg_exists_flankingFaces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_exists_flankingFaces_eq
  {P : PlanarZ2Subgraph}
  {e : kwg_Edge P} :
-- imply
  ∃ f g : Site 2, (hypercubicLattice 2).Adj f g ∧ sharedPrimalEdge f g = kwg_embeddedEdge P e := by
-- proof
  apply StatMech.Ising.kwg_exists_flankingFaces P e

/--
[kwg_flanks_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_flanks_adj_eq
  {P : PlanarZ2Subgraph}
  {e : kwg_Edge P} :
-- imply
  (hypercubicLattice 2).Adj (kwg_flankLeft P e) (kwg_flankRight P e) := by
-- proof
  apply StatMech.Ising.kwg_flanks_adj P e

/--
[kwg_flanks_shared](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_flanks_shared_eq
  {P : PlanarZ2Subgraph}
  {e : kwg_Edge P} :
-- imply
  sharedPrimalEdge (kwg_flankLeft P e) (kwg_flankRight P e) = kwg_embeddedEdge P e := by
-- proof
  apply StatMech.Ising.kwg_flanks_shared P e

/--
[kwg_dualGraph_vertexSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_dualGraph_vertexSet_eq
  {P : PlanarZ2Subgraph} :
-- imply
  (kwg_dualGraph P).vertexSet = Set.univ := by
-- proof
  apply StatMech.Ising.kwg_dualGraph_vertexSet P

/--
[kwg_dualGraph_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_dualGraph_edgeSet_eq
  {P : PlanarZ2Subgraph} :
-- imply
  (kwg_dualGraph P).edgeSet = Set.univ := by
-- proof
  apply StatMech.Ising.kwg_dualGraph_edgeSet P

/--
[kwg_dualGraph_isLink_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_dualGraph_isLink_iff_eq
  {P : PlanarZ2Subgraph}
  {e : kwg_Edge P}
  {x y : kwg_Face P} :
-- imply
  (kwg_dualGraph P).IsLink e x y ↔ kwg_dualEnds P e = s(x, y) := by
-- proof
  apply StatMech.Ising.kwg_dualGraph_isLink_iff P e x y

/--
[kwg_unique_outerFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_unique_outerFace_eq
  {P : PlanarZ2Subgraph} :
-- imply
  ∃! C : kwg_Face P, C.supp.Infinite := by
-- proof
  apply StatMech.Ising.kwg_unique_outerFace P

/--
[kwg_card_face_eq_faceCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_card_face_eq_faceCount_eq
  {P : PlanarZ2Subgraph} :
-- imply
  Nat.card (kwg_Face P) = faceCount P.G := by
-- proof
  apply StatMech.Ising.kwg_card_face_eq_faceCount P

/--
[kwg_card_edge_eq_ncard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_card_edge_eq_ncard_eq
  {P : PlanarZ2Subgraph} :
-- imply
  Nat.card (kwg_Edge P) = P.G.edgeSet.ncard := by
-- proof
  apply StatMech.Ising.kwg_card_edge_eq_ncard P

/--
[kwg_isSplit_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_isSplit_mk_eq
  {c : V → Bool}
  {x y : V} :
-- imply
  kwg_isSplit c s(x, y) ↔ c x ≠ c y := by
-- proof
  apply StatMech.Ising.kwg_isSplit_mk c x y

/--
[kwg_isSplit_iff_bond_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_isSplit_iff_bond_neg_eq
  {c : ConfigSpace V}
  {e : Sym2 V} :
-- imply
  kwg_isSplit c e ↔ bond c e = -1 := by
-- proof
  apply StatMech.Ising.kwg_isSplit_iff_bond_neg c e

/--
[kwg_incidentMod2_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_incidentMod2_mk_eq
  {v x y : V} :
-- imply
  kwg_incidentMod2 v s(x, y) ↔ (x = v ∧ y ≠ v) ∨ (y = v ∧ x ≠ v) := by
-- proof
  apply StatMech.Ising.kwg_incidentMod2_mk v x y

/--
[kwg_incident_iff_componentCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_incident_iff_componentCut_eq
  {P : PlanarZ2Subgraph}
  {e : kwg_Edge P}
  {C : kwg_Face P} :
-- imply
  kwg_incidentMod2 C (kwg_dualEnds P e) ↔ kwg_embeddedEdge P e ∈ jed_cutSet (fun z => (whb_faceRegion (imageGraph P)).connectedComponentMk z = C) := by
-- proof
  apply StatMech.Ising.kwg_incident_iff_componentCut P e C

/--
[kwg_componentCut_subset_imageGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_componentCut_subset_imageGraph_eq
  {P : PlanarZ2Subgraph}
  {C : kwg_Face P} :
-- imply
  jed_cutSet (fun z => (whb_faceRegion (imageGraph P)).connectedComponentMk z = C) ⊆ (imageGraph P).edgeSet := by
-- proof
  apply StatMech.Ising.kwg_componentCut_subset_imageGraph P C

/--
[kwg_componentCut_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_componentCut_even_eq
  {P : PlanarZ2Subgraph}
  {C : kwg_Face P}
  {v : Site 2} :
-- imply
  Even (jce_degree (jed_cutSet (fun z => (whb_faceRegion (imageGraph P)).connectedComponentMk z = C)) v) := by
-- proof
  apply StatMech.Ising.kwg_componentCut_even P C v

/--
[kwg_componentBoundaryGraph_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_componentBoundaryGraph_degree_eq
  {P : PlanarZ2Subgraph}
  {C : kwg_Face P}
  {x : P.V} :
-- imply
  (kwg_componentBoundaryGraph P C).degree x = jce_degree (jed_cutSet (fun z => (whb_faceRegion (imageGraph P)).connectedComponentMk z = C)) (P.emb x) := by
-- proof
  apply StatMech.Ising.kwg_componentBoundaryGraph_degree P C x

/--
[kwg_componentBoundaryGraph_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_componentBoundaryGraph_even_eq
  {P : PlanarZ2Subgraph}
  {C : kwg_Face P}
  {x : P.V} :
-- imply
  Even ((kwg_componentBoundaryGraph P C).degree x) := by
-- proof
  apply StatMech.Ising.kwg_componentBoundaryGraph_even P C x

/--
[kwg_mem_cutSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_mem_cutSet_eq
  [Empty.Finite E]
  {ends : E → Sym2 V}
  {c : V → Bool}
  {e : E} :
-- imply
  e ∈ kwg_cutSet ends c ↔ kwg_isSplit c (ends e) := by
-- proof
  apply StatMech.Ising.kwg_mem_cutSet ends c e

/--
[kwg_IsEven_iff_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_IsEven_iff_degree_eq
  [DecidableEq E]
  {ends : E → Sym2 V}
  {F : Finset E} :
-- imply
  kwg_IsEven ends F ↔ ∀ v, Even (kwg_degree ends F v) := by
-- proof
  apply StatMech.Ising.kwg_IsEven_iff_degree ends F

/--
[kwg_IsEven_sdiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_IsEven_sdiff_eq
  [DecidableEq E]
  {ends : E → Sym2 V}
  {F S : Finset E}
-- given
  (hSF : S ⊆ F)
  (hF : kwg_IsEven ends F)
  (hS : kwg_IsEven ends S) :
-- imply
  kwg_IsEven ends (F \ S) := by
-- proof
  apply StatMech.Ising.kwg_IsEven_sdiff ends hSF hF hS

/--
[kwg_degree_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_degree_insert_eq
  [DecidableEq V]
  [DecidableEq E]
  {ends : E → Sym2 V}
  {F : Finset E}
  {e : E}
  {v : V}
-- given
  (he : e ∉ F) :
-- imply
  kwg_degree ends (insert e F) v = kwg_degree ends F v + (if kwg_incidentMod2 v (ends e) then 1 else 0) := by
-- proof
  apply StatMech.Ising.kwg_degree_insert ends F e he v

/--
[kwg_prod_bond_eq_prod_pow_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_prod_bond_eq_prod_pow_degree_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq E]
  {ends : E → Sym2 V}
  {c : ConfigSpace V}
  {F : Finset E} :
-- imply
  (∏ e ∈ F, bond c (ends e)) = ∏ v : V, (spin c v) ^ (kwg_degree ends F v) := by
-- proof
  apply StatMech.Ising.kwg_prod_bond_eq_prod_pow_degree ends c F

/--
[kwg_even_split_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_even_split_card_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq E]
  {ends : E → Sym2 V}
  {F : Finset E}
  {c : V → Bool}
-- given
  (hev : kwg_IsEven ends F) :
-- imply
  Even (F.filter (fun e => kwg_isSplit c (ends e))).card := by
-- proof
  apply StatMech.Ising.kwg_even_split_card ends F c hev

/--
[kwg_faceInside_eq_of_regionReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_faceInside_eq_of_regionReachable_eq
  {P : PlanarZ2Subgraph}
  {x : P.V}
  {p : P.G.Walk x x}
  {a b : Site 2}
-- given
  (hab : (whb_faceRegion (imageGraph P)).Reachable a b) :
-- imply
  (fwr_faceInside (kwg_latticeWalk P p) a ↔ fwr_faceInside (kwg_latticeWalk P p) b) := by
-- proof
  apply StatMech.Ising.kwg_faceInside_eq_of_regionReachable P p hab

/--
[kwg_walkFaceColour_split_iff_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_walkFaceColour_split_iff_odd_eq
  {P : PlanarZ2Subgraph}
  {x : P.V}
  {p : P.G.Walk x x}
  {e : kwg_Edge P} :
-- imply
  kwg_isSplit (kwg_walkFaceColour P p) (kwg_dualEnds P e) ↔ Odd ((kwg_latticeWalk P p).edges.count (kwg_embeddedEdge P e)) := by
-- proof
  apply StatMech.Ising.kwg_walkFaceColour_split_iff_odd P p e

/--
[kwg_even_sum_iff_even_odd_filter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_even_sum_iff_even_odd_filter_eq
  [DecidableEq E]
  {F : Finset E}
  {n : E → ℕ} :
-- imply
  Even (∑ e ∈ F, n e) ↔ Even (F.filter (fun e => Odd (n e))).card := by
-- proof
  apply StatMech.Ising.kwg_even_sum_iff_even_odd_filter F n

/--
[kwg_walkParity_eq_decide_odd_countP](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_walkParity_eq_decide_odd_countP_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {D : Finset (Sym2 V)}
  {x y : V}
  {p : G.Walk x y} :
-- imply
  walkParity G D p = decide (Odd (p.edges.countP (fun e => decide (e ∈ D)))) := by
-- proof
  apply StatMech.Ising.kwg_walkParity_eq_decide_odd_countP D p

/--
[kwg_latticeWalk_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_latticeWalk_count_eq
  {P : PlanarZ2Subgraph}
  {x y : P.V}
  {p : P.G.Walk x y}
  {e : Sym2 P.V} :
-- imply
  (kwg_latticeWalk P p).edges.count (Sym2.map P.emb e) = p.edges.count e := by
-- proof
  apply StatMech.Ising.kwg_latticeWalk_count P p e

/--
[kwg_primal_incident_iff_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_primal_incident_iff_mem_eq
  {P : PlanarZ2Subgraph}
  {e : kwg_Edge P}
  {x : P.V} :
-- imply
  kwg_incidentMod2 x (kwg_primalEnds P e) ↔ x ∈ e.1 := by
-- proof
  apply StatMech.Ising.kwg_primal_incident_iff_mem P e x

/--
[kwg_mem_primalEdgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_mem_primalEdgeFinset_eq
  {P : PlanarZ2Subgraph}
  {F : Finset (kwg_Edge P)}
  {e : kwg_Edge P} :
-- imply
  e.1 ∈ kwg_primalEdgeFinset P F ↔ e ∈ F := by
-- proof
  apply StatMech.Ising.kwg_mem_primalEdgeFinset P F e

/--
[kwg_sum_count_eq_countP](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_sum_count_eq_countP_eq
  [DecidableEq A]
  {D : Finset A}
  {l : List A} :
-- imply
  (∑ a ∈ D, l.count a) = l.countP (fun a => decide (a ∈ D)) := by
-- proof
  apply StatMech.Ising.kwg_sum_count_eq_countP D l

/--
[kwg_dualEven_evenOnCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_dualEven_evenOnCycles_eq
  {P : PlanarZ2Subgraph}
  {F : Finset (kwg_Edge P)}
-- given
  (hev : kwg_IsEven (kwg_dualEnds P) F) :
-- imply
  EvenOnCycles P.G (kwg_primalEdgeFinset P F) := by
-- proof
  apply StatMech.Ising.kwg_dualEven_evenOnCycles P F hev

/--
[kwg_walkParity_copy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_walkParity_copy_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {D : Finset (Sym2 V)}
  {u v u' v' : V}
  {p : G.Walk u v}
-- given
  (hu : u = u')
  (hv : v = v') :
-- imply
  walkParity G D (p.copy hu hv) = walkParity G D p := by
-- proof
  apply StatMech.Ising.kwg_walkParity_copy p hu hv

/--
[kwg_componentParityColour_adj_xor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_componentParityColour_adj_xor_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {D : Finset (Sym2 V)}
  {x y : V}
-- given
  (hev : EvenOnCycles G D)
  (hxy : G.Adj x y) :
-- imply
  (kwg_componentParityColour G D x).xor (kwg_componentParityColour G D y) = decide (s(x, y) ∈ D) := by
-- proof
  apply StatMech.Ising.kwg_componentParityColour_adj_xor hev hxy

/--
[kwg_exists_colour_of_evenOnCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_exists_colour_of_evenOnCycles_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {D : Finset (Sym2 V)}
-- given
  (hsub : D ⊆ G.edgeFinset)
  (hev : EvenOnCycles G D) :
-- imply
  ∃ c : V → Bool, cutEdges G c = D := by
-- proof
  apply StatMech.Ising.kwg_exists_colour_of_evenOnCycles hsub hev

/--
[kwg_dualEven_exists_primalCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_dualEven_exists_primalCut_eq
  {P : PlanarZ2Subgraph}
  {F : Finset (kwg_Edge P)}
-- given
  (hev : kwg_IsEven (kwg_dualEnds P) F) :
-- imply
  ∃ c : ConfigSpace P.V, kwg_cutSet (kwg_primalEnds P) c = F := by
-- proof
  apply StatMech.Ising.kwg_dualEven_exists_primalCut P F hev

/--
[kwg_componentIncident_isEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_componentIncident_isEven_eq
  {P : PlanarZ2Subgraph}
  {C : kwg_Face P} :
-- imply
  by classical letI : Fintype P.V := Fintype.ofFinite P.V letI : Fintype (kwg_Face P) := Fintype.ofFinite (kwg_Face P) exact kwg_IsEven (kwg_primalEnds P) ((kwg_allEdges P).filter (fun e => kwg_incidentMod2 C (kwg_dualEnds P e))) := by
-- proof
  apply StatMech.Ising.kwg_componentIncident_isEven P C

/--
[kwg_primalCut_isEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_primalCut_isEven_eq
  {P : PlanarZ2Subgraph}
  {c : ConfigSpace P.V} :
-- imply
  kwg_IsEven (kwg_dualEnds P) (kwg_cutSet (kwg_primalEnds P) c) := by
-- proof
  apply StatMech.Ising.kwg_primalCut_isEven P c

/--
[kwg_sum_prod_bond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_sum_prod_bond_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq E]
  {ends : E → Sym2 V}
  {F : Finset E} :
-- imply
  (∑ c : ConfigSpace V, ∏ e ∈ F, bond c (ends e)) = if kwg_IsEven ends F then (2 : ℝ) ^ Fintype.card V else 0 := by
-- proof
  apply StatMech.Ising.kwg_sum_prod_bond ends F

/--
[kwg_isingZ_high_temp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_isingZ_high_temp_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype E]
  [DecidableEq E]
  {ends : E → Sym2 V}
  {β : ℝ} :
-- imply
  kwg_isingZ ends β = (2 : ℝ) ^ Fintype.card V * (Real.cosh β) ^ Fintype.card E * ∑ F : Finset E, if kwg_IsEven ends F then (Real.tanh β) ^ F.card else 0 := by
-- proof
  apply StatMech.Ising.kwg_isingZ_high_temp ends β

/--
[kwg_primalCut_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_primalCut_card_eq
  {P : PlanarZ2Subgraph}
  {c : ConfigSpace P.V} :
-- imply
  (kwg_cutSet (kwg_primalEnds P) c).card = (cutEdges P.G c).card := by
-- proof
  apply StatMech.Ising.kwg_primalCut_card P c

/--
[kwg_primalEdgeFinset_cutSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_primalEdgeFinset_cutSet_eq
  {P : PlanarZ2Subgraph}
  {c : ConfigSpace P.V} :
-- imply
  kwg_primalEdgeFinset P (kwg_cutSet (kwg_primalEnds P) c) = cutEdges P.G c := by
-- proof
  apply StatMech.Ising.kwg_primalEdgeFinset_cutSet P c

/--
[kwg_cutSet_eq_iff_cutEdges_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_cutSet_eq_iff_cutEdges_eq_eq
  {P : PlanarZ2Subgraph}
  {c d : ConfigSpace P.V} :
-- imply
  kwg_cutSet (kwg_primalEnds P) c = kwg_cutSet (kwg_primalEnds P) d ↔ cutEdges P.G c = cutEdges P.G d := by
-- proof
  apply StatMech.Ising.kwg_cutSet_eq_iff_cutEdges_eq P c d

/--
[kwg_componentTwist_cutEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_componentTwist_cutEdges_eq
  {P : PlanarZ2Subgraph}
  {c : ConfigSpace P.V}
  {a : P.G.ConnectedComponent → Bool} :
-- imply
  cutEdges P.G (kwg_componentTwist P c a) = cutEdges P.G c := by
-- proof
  apply StatMech.Ising.kwg_componentTwist_cutEdges P c a

/--
[kwg_primalCut_fiber_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_primalCut_fiber_card_eq
  {P : PlanarZ2Subgraph}
  {c : ConfigSpace P.V} :
-- imply
  (Finset.univ.filter (fun d : ConfigSpace P.V => kwg_cutSet (kwg_primalEnds P) d = kwg_cutSet (kwg_primalEnds P) c)).card = 2 ^ Nat.card P.G.ConnectedComponent := by
-- proof
  apply StatMech.Ising.kwg_primalCut_fiber_card P c

/--
[kwg_primalCut_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_primalCut_sum_eq
  {P : PlanarZ2Subgraph}
  {t : ℝ} :
-- imply
  by letI : Fintype P.V := Fintype.ofFinite P.V exact (∑ c : ConfigSpace P.V, t ^ (kwg_cutSet (kwg_primalEnds P) c).card) = ∑ c : ConfigSpace P.V, t ^ (cutEdges P.G c).card := by
-- proof
  apply StatMech.Ising.kwg_primalCut_sum P t

/--
[kwg_geometricCutCycleDuality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_geometricCutCycleDuality_eq
  {P : PlanarZ2Subgraph} :
-- imply
  kwg_GeometricCutCycleDuality P := by
-- proof
  apply StatMech.Ising.kwg_geometricCutCycleDuality P

/--
[kwg_cutEdges_eq_of_nonempty_subset_of_colourSidesConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_cutEdges_eq_of_nonempty_subset_of_colourSidesConnected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {c d : V → Bool}
-- given
  (hcconn : kwg_ColourSidesConnected G c)
  (hsub : cutEdges G d ⊆ cutEdges G c)
  (hne : (cutEdges G d).Nonempty) :
-- imply
  cutEdges G d = cutEdges G c := by
-- proof
  apply StatMech.Ising.kwg_cutEdges_eq_of_nonempty_subset_of_colourSidesConnected G c d hcconn hsub hne

/--
[kwg_dualEven_subset_bond_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_dualEven_subset_bond_eq_eq
  {P : PlanarZ2Subgraph}
  {c : ConfigSpace P.V}
  {F : Finset (kwg_Edge P)}
-- given
  (hcconn : kwg_ColourSidesConnected P.G c)
  (hsub : F ⊆ kwg_cutSet (kwg_primalEnds P) c)
  (hne : F.Nonempty)
  (heven : kwg_IsEven (kwg_dualEnds P) F) :
-- imply
  F = kwg_cutSet (kwg_primalEnds P) c := by
-- proof
  apply StatMech.Ising.kwg_dualEven_subset_bond_eq P c hcconn F hsub hne heven

/--
[kwg_subdivGraph_face_port_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_subdivGraph_face_port_false_eq
  {ends : E → Sym2 V}
  {v : V}
  {e : E} :
-- imply
  (kwg_subdivGraph ends).Adj (Sum.inl v) (Sum.inr (e, false)) ↔ v = (ends e).out.1 := by
-- proof
  apply StatMech.Ising.kwg_subdivGraph_face_port_false ends v e

/--
[kwg_subdivGraph_face_port_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_subdivGraph_face_port_true_eq
  {ends : E → Sym2 V}
  {v : V}
  {e : E} :
-- imply
  (kwg_subdivGraph ends).Adj (Sum.inl v) (Sum.inr (e, true)) ↔ v = (ends e).out.2 := by
-- proof
  apply StatMech.Ising.kwg_subdivGraph_face_port_true ends v e

/--
[kwg_subdivGraph_ports](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_subdivGraph_ports_eq
  {ends : E → Sym2 V}
  {e e' : E}
  {b b' : Bool} :
-- imply
  (kwg_subdivGraph ends).Adj (Sum.inr (e, b)) (Sum.inr (e', b')) ↔ e = e' ∧ b ≠ b' := by
-- proof
  apply StatMech.Ising.kwg_subdivGraph_ports ends e e' b b'

/--
[kwg_subdivGraph_port_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_subdivGraph_port_degree_eq
  [Empty.Finite V]
  [Empty.Finite E]
  [DecidableEq V]
  [DecidableEq E]
  {ends : E → Sym2 V}
  {e : E}
  {b : Bool} :
-- imply
  (kwg_subdivGraph ends).degree (Sum.inr (e, b)) = 2 := by
-- proof
  apply StatMech.Ising.kwg_subdivGraph_port_degree ends e b

/--
[kwg_subdivGraph_face_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_subdivGraph_face_degree_eq
  [Fintype V]
  [Fintype E]
  [DecidableEq V]
  [DecidableEq E]
  {ends : E → Sym2 V}
  {v : V} :
-- imply
  (kwg_subdivGraph ends).degree (Sum.inl v) = ((Finset.univ : Finset E).filter (fun e => (ends e).out.1 = v)).card + ((Finset.univ : Finset E).filter (fun e => (ends e).out.2 = v)).card := by
-- proof
  apply StatMech.Ising.kwg_subdivGraph_face_degree ends v

/--
[kwg_sum_degree_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_sum_degree_even_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq E]
  {ends : E → Sym2 V}
  {F : Finset E} :
-- imply
  Even (∑ v : V, kwg_degree ends F v) := by
-- proof
  apply StatMech.Ising.kwg_sum_degree_even ends F

/--
[kwg_minimalEven_nonOuter_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_minimalEven_nonOuter_reachable_eq
  [Fintype V]
  [Fintype E]
  [DecidableEq V]
  [DecidableEq E]
  {ends : E → Sym2 V}
  {outer : V}
  {v w : V}
-- given
  (hne : Nonempty E)
  (heven : kwg_IsEven ends Finset.univ)
  (hmin : ∀ S : Finset E, S.Nonempty → kwg_IsEven ends S → S = Finset.univ)
  (hvout : v ≠ outer)
  (hwout : w ≠ outer)
  (hvinc : ∃ e : E, kwg_incidentMod2 v (ends e))
  (hwinc : ∃ e : E, kwg_incidentMod2 w (ends e)) :
-- imply
  (kwg_deleteVertexGraph (kwg_faceSupportGraph ends) outer).Reachable v w := by
-- proof
  apply StatMech.Ising.kwg_minimalEven_nonOuter_reachable ends outer hne heven hmin hvout hwout hvinc hwinc

/--
[kwg_minimalEvenFinset_nonOuter_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_minimalEvenFinset_nonOuter_reachable_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq E]
  {ends : E → Sym2 V}
  {F : Finset E}
  {outer : V}
  {v w : V}
-- given
  (hne : F.Nonempty)
  (heven : kwg_IsEven ends F)
  (hmin : ∀ S : Finset E, S ⊆ F → S.Nonempty → kwg_IsEven ends S → S = F)
  (hvout : v ≠ outer)
  (hwout : w ≠ outer)
  (hvinc : ∃ e ∈ F, kwg_incidentMod2 v (ends e))
  (hwinc : ∃ e ∈ F, kwg_incidentMod2 w (ends e)) :
-- imply
  (kwg_deleteVertexGraph (kwg_faceSupportGraph (fun e : ↑F => ends e.1)) outer).Reachable v w := by
-- proof
  apply StatMech.Ising.kwg_minimalEvenFinset_nonOuter_reachable ends F outer hne heven hmin hvout hwout hvinc hwinc

/--
[kwg_exists_minimalEvenFinset_subset_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_exists_minimalEvenFinset_subset_mem_eq
  [DecidableEq E]
  {ends : E → Sym2 V}
  {F : Finset E}
  {e : E}
-- given
  (heF : e ∈ F)
  (hF : kwg_IsEven ends F) :
-- imply
  ∃ S : Finset E, S ⊆ F ∧ e ∈ S ∧ S.Nonempty ∧ kwg_IsEven ends S ∧ ∀ T : Finset E, T ⊆ S → T.Nonempty → kwg_IsEven ends T → T = S := by
-- proof
  apply StatMech.Ising.kwg_exists_minimalEvenFinset_subset_mem ends heF hF

/--
[kwg_exists_minimalEvenFinset_peel_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_exists_minimalEvenFinset_peel_mem_eq
  [DecidableEq E]
  {ends : E → Sym2 V}
  {F : Finset E}
  {e : E}
-- given
  (heF : e ∈ F)
  (hF : kwg_IsEven ends F) :
-- imply
  ∃ S R : Finset E, S ⊆ F ∧ e ∈ S ∧ S.Nonempty ∧ kwg_IsEven ends S ∧ (∀ T : Finset E, T ⊆ S → T.Nonempty → kwg_IsEven ends T → T = S) ∧ R = F \ S ∧ kwg_IsEven ends R ∧ Disjoint S R ∧ S ∪ R = F := by
-- proof
  apply StatMech.Ising.kwg_exists_minimalEvenFinset_peel_mem ends heF hF

/--
[kwg_subdivGraph_face_degree_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_subdivGraph_face_degree_even_eq
  [Fintype V]
  [Fintype E]
  [DecidableEq V]
  [DecidableEq E]
  {ends : E → Sym2 V}
  {v : V}
-- given
  (heven : kwg_IsEven ends Finset.univ) :
-- imply
  Even ((kwg_subdivGraph ends).degree (Sum.inl v)) := by
-- proof
  apply StatMech.Ising.kwg_subdivGraph_face_degree_even ends heven v

/--
[kwg_subdivGraph_reachable_port_of_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_subdivGraph_reachable_port_of_incident_eq
  {ends : E → Sym2 V}
  {v : V}
  {e : E}
  {b : Bool}
-- given
  (hinc : kwg_incidentMod2 v (ends e)) :
-- imply
  (kwg_subdivGraph ends).Reachable (Sum.inl v) (Sum.inr (e, b)) := by
-- proof
  apply StatMech.Ising.kwg_subdivGraph_reachable_port_of_incident ends hinc b

/--
[kwg_minimalEven_edgePorts_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_minimalEven_edgePorts_reachable_eq
  [Fintype V]
  [Fintype E]
  [DecidableEq V]
  [DecidableEq E]
  {ends : E → Sym2 V}
-- given
  (hne : Nonempty E)
  (heven : kwg_IsEven ends Finset.univ)
  (hmin : ∀ S : Finset E, S.Nonempty → kwg_IsEven ends S → S = Finset.univ) :
-- imply
  ∀ e e' : E, ∀ b b' : Bool, (kwg_subdivGraph ends).Reachable (Sum.inr (e, b)) (Sum.inr (e', b')) := by
-- proof
  apply StatMech.Ising.kwg_minimalEven_edgePorts_reachable ends hne heven hmin

/--
[kwg_cutEvenMatching_of_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_cutEvenMatching_of_duality_eq
  {P : PlanarZ2Subgraph}
  {t mult : ℝ}
-- given
  (hdual : kwg_GeometricCutCycleDuality P)
  (hfib : ∀ F : Finset (kwg_Edge P), kwg_IsEven (kwg_dualEnds P) F → ((Finset.univ.filter (fun c : ConfigSpace P.V => kwg_cutSet (kwg_primalEnds P) c = F)).card : ℝ) = mult) :
-- imply
  kwg_GeometricCutEvenMatching P t mult := by
-- proof
  apply StatMech.Ising.kwg_cutEvenMatching_of_duality P t mult hdual hfib

/--
[kwg_geometricCutEvenMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_geometricCutEvenMatching_eq
  {P : PlanarZ2Subgraph}
  {t : ℝ} :
-- imply
  kwg_GeometricCutEvenMatching P t ((2 : ℝ) ^ Nat.card P.G.ConnectedComponent) := by
-- proof
  apply StatMech.Ising.kwg_geometricCutEvenMatching P t

/--
[kwg_geometricCutEvenMatching_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_geometricCutEvenMatching_of_connected_eq
  {P : PlanarZ2Subgraph}
  {t : ℝ}
-- given
  (hconn : P.G.Connected) :
-- imply
  kwg_GeometricCutEvenMatching P t 2 := by
-- proof
  apply StatMech.Ising.kwg_geometricCutEvenMatching_of_connected P hconn t

/--
[kwg_dualContourMatching_of_cutMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_dualContourMatching_of_cutMatching_eq
  {P : PlanarZ2Subgraph}
  {β βstar : ℝ}
-- given
  (htemp : Real.tanh βstar = Real.exp (-2 * β))
  (hmatch : kwg_GeometricCutEvenMatching P (Real.exp (-2 * β)) 2) :
-- imply
  kwg_DualContourMatching P β βstar ((2 : ℝ) ^ Nat.card (kwg_Face P) * (Real.cosh βstar) ^ Nat.card (kwg_Edge P) / (Real.exp (β * P.G.edgeSet.ncard) * 2)) := by
-- proof
  apply StatMech.Ising.kwg_dualContourMatching_of_cutMatching P β βstar htemp hmatch

/--
[kwg_isingZ_duality_of_cutMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_isingZ_duality_of_cutMatching_eq
  {P : PlanarZ2Subgraph}
  {β βstar : ℝ}
-- given
  (htemp : Real.tanh βstar = Real.exp (-2 * β))
  (hmatch : kwg_GeometricCutEvenMatching P (Real.exp (-2 * β)) 2) :
-- imply
  by letI : Fintype P.V := Fintype.ofFinite P.V letI : Fintype (kwg_Face P) := Fintype.ofFinite (kwg_Face P) letI : DecidableEq (kwg_Face P) := Classical.decEq _ exact kwg_isingZ (kwg_dualEnds P) βstar = ((2 : ℝ) ^ Nat.card (kwg_Face P) * (Real.cosh βstar) ^ Nat.card (kwg_Edge P) / (Real.exp (β * P.G.edgeSet.ncard) * 2)) * isingZ P.G β 0 := by
-- proof
  apply StatMech.Ising.kwg_isingZ_duality_of_cutMatching P β βstar htemp hmatch

/--
[kwg_isingZ_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean)
-/
@[path]
private lemma kwg_isingZ_duality_eq
  {P : PlanarZ2Subgraph}
  {β βstar : ℝ}
-- given
  (htemp : Real.tanh βstar = Real.exp (-2 * β)) :
-- imply
  kwg_isingZ (kwg_dualEnds P) βstar = ((2 : ℝ) ^ Nat.card (kwg_Face P) * (Real.cosh βstar) ^ Nat.card (kwg_Edge P) / (Real.exp (β * P.G.edgeSet.ncard) * (2 : ℝ) ^ Nat.card P.G.ConnectedComponent)) * isingZ P.G β 0 := by
-- proof
  apply StatMech.Ising.kwg_isingZ_duality P β βstar htemp


-- created on 2026-10-23
