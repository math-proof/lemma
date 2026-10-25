import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempKacWard.Part5
open Finset SimpleGraph StatMech StatMech.Onsager


/--
[kwg_subdivCentralEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_subdivCentralEdge_injective_eq
  [Fintype V]
  [Fintype E] :
-- imply
  Function.Injective (kwg_subdivCentralEdge : E -> kwg_SubdivEdge V E) := by
-- proof
  apply StatMech.Onsager.kwg_subdivCentralEdge_injective

/--
[kwg_subdivCentralEdge_mem_gadget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_subdivCentralEdge_mem_gadget_eq
  [Fintype V]
  [Fintype E]
  {e e' : E}
-- given
  (ends : E -> Sym2 V) :
-- imply
  kwg_subdivCentralEdge e' ∈ kwg_subdivGadgetEdges ends e ↔ e' = e := by
-- proof
  apply StatMech.Onsager.kwg_subdivCentralEdge_mem_gadget ends e e'

/--
[kwg_subdivCentralEdge_mem_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_subdivCentralEdge_mem_lift_eq
  [Fintype V]
  [Fintype E]
  {F : Finset E}
  {e : E}
-- given
  (ends : E -> Sym2 V) :
-- imply
  kwg_subdivCentralEdge e ∈ kwg_subdivLift ends F ↔ e ∈ F := by
-- proof
  apply StatMech.Onsager.kwg_subdivCentralEdge_mem_lift ends F e

/--
[kwg_subdivGraph_mem_edgeFinset_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_subdivGraph_mem_edgeFinset_iff_eq
  [Fintype V]
  [Fintype E]
  {edge : kwg_SubdivEdge V E}
-- given
  (ends : E -> Sym2 V) :
-- imply
  edge ∈ (kwg_subdivGraph ends).edgeFinset ↔ ∃ e : E, edge ∈ kwg_subdivGadgetEdges ends e := by
-- proof
  apply StatMech.Onsager.kwg_subdivGraph_mem_edgeFinset_iff ends edge

/--
[kwg_subdivLift_subset_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_subdivLift_subset_edgeFinset_eq
  [Fintype V]
  [Fintype E]
  {F : Finset E}
-- given
  (ends : E -> Sym2 V) :
-- imply
  kwg_subdivLift ends F ⊆ (kwg_subdivGraph ends).edgeFinset := by
-- proof
  apply StatMech.Onsager.kwg_subdivLift_subset_edgeFinset ends F

/--
[kwg_subdivGraph_neighborFinset_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_subdivGraph_neighborFinset_false_eq
  [Fintype V]
  [Fintype E]
  {e : E}
-- given
  (ends : E -> Sym2 V) :
-- imply
  (kwg_subdivGraph ends).neighborFinset (Sum.inr (e, false)) = {Sum.inl (ends e).out.1, Sum.inr (e, true)} := by
-- proof
  apply StatMech.Onsager.kwg_subdivGraph_neighborFinset_false ends e

/--
[kwg_subdivGraph_neighborFinset_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_subdivGraph_neighborFinset_true_eq
  [Fintype V]
  [Fintype E]
  {e : E}
-- given
  (ends : E -> Sym2 V) :
-- imply
  (kwg_subdivGraph ends).neighborFinset (Sum.inr (e, true)) = {Sum.inr (e, false), Sum.inl (ends e).out.2} := by
-- proof
  apply StatMech.Onsager.kwg_subdivGraph_neighborFinset_true ends e

/--
[kwg_evenSubgraph_gadget_membership](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_evenSubgraph_gadget_membership_eq
  [Fintype V]
  [Fintype E]
  {H : Finset (kwg_SubdivEdge V E)}
  {e : E}
-- given
  (ends : E -> Sym2 V)
  (hH : H ∈ evenSubgraphs (kwg_subdivGraph ends)) :
-- imply
  kwg_subdivLeftEdge ends e ∈ H ↔ kwg_subdivCentralEdge e ∈ H := by
-- proof
  apply StatMech.Onsager.kwg_evenSubgraph_gadget_membership ends H hH e

/--
[kwg_evenSubgraph_gadget_membership_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_evenSubgraph_gadget_membership_right_eq
  [Fintype V]
  [Fintype E]
  {H : Finset (kwg_SubdivEdge V E)}
  {e : E}
-- given
  (ends : E -> Sym2 V)
  (hH : H ∈ evenSubgraphs (kwg_subdivGraph ends)) :
-- imply
  kwg_subdivRightEdge ends e ∈ H ↔ kwg_subdivCentralEdge e ∈ H := by
-- proof
  apply StatMech.Onsager.kwg_evenSubgraph_gadget_membership_right ends H hH e

/--
[kwg_subdivExtract_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_subdivExtract_lift_eq
  [Fintype V]
  [Fintype E]
  {F : Finset E}
-- given
  (ends : E -> Sym2 V) :
-- imply
  kwg_subdivExtract (kwg_subdivLift ends F) = F := by
-- proof
  apply StatMech.Onsager.kwg_subdivExtract_lift ends F

/--
[kwg_subdivLift_extract_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_subdivLift_extract_of_even_eq
  [Fintype V]
  [Fintype E]
  {H : Finset (kwg_SubdivEdge V E)}
-- given
  (ends : E -> Sym2 V)
  (hH : H ∈ evenSubgraphs (kwg_subdivGraph ends)) :
-- imply
  kwg_subdivLift ends (kwg_subdivExtract H) = H := by
-- proof
  apply StatMech.Onsager.kwg_subdivLift_extract_of_even ends H hH

/--
[kwg_subdivLeftEdge_mem_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_subdivLeftEdge_mem_lift_eq
  [Fintype V]
  [Fintype E]
  {F : Finset E}
  {e : E}
-- given
  (ends : E -> Sym2 V) :
-- imply
  kwg_subdivLeftEdge ends e ∈ kwg_subdivLift ends F ↔ e ∈ F := by
-- proof
  apply StatMech.Onsager.kwg_subdivLeftEdge_mem_lift ends F e

/--
[kwg_subdivRightEdge_mem_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_subdivRightEdge_mem_lift_eq
  [Fintype V]
  [Fintype E]
  {F : Finset E}
  {e : E}
-- given
  (ends : E -> Sym2 V) :
-- imply
  kwg_subdivRightEdge ends e ∈ kwg_subdivLift ends F ↔ e ∈ F := by
-- proof
  apply StatMech.Onsager.kwg_subdivRightEdge_mem_lift ends F e

/--
[kwg_incCount_subdivLift_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_incCount_subdivLift_face_eq
  [Fintype V]
  [Fintype E]
  {F : Finset E}
  {v : V}
-- given
  (ends : E -> Sym2 V) :
-- imply
  incCount (kwg_subdivLift ends F) (Sum.inl v) = (F.filter (fun e => (ends e).out.1 = v)).card + (F.filter (fun e => (ends e).out.2 = v)).card := by
-- proof
  apply StatMech.Onsager.kwg_incCount_subdivLift_face ends F v

/--
[kwg_incCount_subdivLift_port](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_incCount_subdivLift_port_eq
  [Fintype V]
  [Fintype E]
  {F : Finset E}
  {e : E}
  {b : Bool}
-- given
  (ends : E -> Sym2 V) :
-- imply
  incCount (kwg_subdivLift ends F) (Sum.inr (e, b)) = if e ∈ F then 2 else 0 := by
-- proof
  apply StatMech.Onsager.kwg_incCount_subdivLift_port ends F e b

/--
[kwg_subdivLift_isEven_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_subdivLift_isEven_iff_eq
  [Fintype V]
  [Fintype E]
  {F : Finset E}
-- given
  (ends : E -> Sym2 V) :
-- imply
  IsEvenSubgraph (kwg_subdivLift ends F) ↔ kwg_IsEven ends F := by
-- proof
  apply StatMech.Onsager.kwg_subdivLift_isEven_iff ends F

/--
[kwg_subdivLift_mem_evenSubgraphs_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_subdivLift_mem_evenSubgraphs_iff_eq
  [Fintype V]
  [Fintype E]
  {F : Finset E}
-- given
  (ends : E -> Sym2 V) :
-- imply
  kwg_subdivLift ends F ∈ evenSubgraphs (kwg_subdivGraph ends) ↔ kwg_IsEven ends F := by
-- proof
  apply StatMech.Onsager.kwg_subdivLift_mem_evenSubgraphs_iff ends F

/--
[kwg_subdivWeight_central](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_subdivWeight_central_eq
  [Fintype V]
  [Fintype E]
  {e : E}
-- given
  (x : E -> ℂ) :
-- imply
  (kwg_subdivWeight (V := V) x) (kwg_subdivCentralEdge e) = x e := by
-- proof
  apply StatMech.Onsager.kwg_subdivWeight_central x e

/--
[kwg_subdivWeight_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_subdivWeight_left_eq
  [Fintype V]
  [Fintype E]
  {e : E}
-- given
  (ends : E -> Sym2 V)
  (x : E -> ℂ) :
-- imply
  (kwg_subdivWeight (V := V) x) (kwg_subdivLeftEdge ends e) = 1 := by
-- proof
  apply StatMech.Onsager.kwg_subdivWeight_left ends x e

/--
[kwg_subdivWeight_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_subdivWeight_right_eq
  [Fintype V]
  [Fintype E]
  {e : E}
-- given
  (ends : E -> Sym2 V)
  (x : E -> ℂ) :
-- imply
  (kwg_subdivWeight (V := V) x) (kwg_subdivRightEdge ends e) = 1 := by
-- proof
  apply StatMech.Onsager.kwg_subdivWeight_right ends x e

/--
[kwg_subdivLift_weight_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_subdivLift_weight_product_eq
  [Fintype V]
  [Fintype E]
  {F : Finset E}
-- given
  (ends : E -> Sym2 V)
  (x : E -> ℂ) :
-- imply
  ∏ edge ∈ kwg_subdivLift ends F, kwg_subdivWeight (V := V) x edge = ∏ e ∈ F, x e := by
-- proof
  apply StatMech.Onsager.kwg_subdivLift_weight_product ends x F

/--
[kwg_indexedEvenPolynomial_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_indexedEvenPolynomial_eq_sum_eq
  [Fintype V]
  [Fintype E]
-- given
  (ends : E -> Sym2 V)
  (x : E -> ℂ) :
-- imply
  kwg_indexedEvenPolynomial ends x = ∑ F : KWGIndexedEvenSet ends, ∏ e ∈ F.1, x e := by
-- proof
  apply StatMech.Onsager.kwg_indexedEvenPolynomial_eq_sum ends x

/--
[kwg_subdiv_evenPolynomial_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_subdiv_evenPolynomial_eq_eq
  [Fintype V]
  [Fintype E]
-- given
  (ends : E -> Sym2 V)
  (x : E -> ℂ) :
-- imply
  kwEvenPolynomial (kwg_subdivGraph ends) (kwg_subdivWeight (V := V) x) = kwg_indexedEvenPolynomial ends x := by
-- proof
  apply StatMech.Onsager.kwg_subdiv_evenPolynomial_eq ends x

/--
[kwg_subdiv_kacWard_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_subdiv_kacWard_det_eq
  [Fintype V]
  [Fintype E]
  {embedding : KWStraightLineEmbedding (kwg_subdivGraph ends)}
-- given
  (ends : E -> Sym2 V)
  (x : E -> ℂ) :
-- imply
  (1 - kwGraphTransition (kwg_subdivGraph ends) (kwg_subdivWeight (V := V) x) embedding.turnPhase).det = (kwg_indexedEvenPolynomial ends x) ^ 2 := by
-- proof
  apply StatMech.Onsager.kwg_subdiv_kacWard_det ends embedding x

/--
[ofReal_kwg_lowTempDualSum_eq_indexedEvenPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma ofReal_kwg_lowTempDualSum_eq_indexedEvenPolynomial_eq
  [Fintype V]
  [Fintype E]
  {P : PlanarZ2Subgraph}
  {beta : Real} :
-- imply
  (kwg_lowTempDualSum P beta : ℂ) = kwg_indexedEvenPolynomial (kwg_dualEnds P) (fun _ => (Real.exp (-2 * beta) : ℂ)) := by
-- proof
  apply StatMech.Onsager.ofReal_kwg_lowTempDualSum_eq_indexedEvenPolynomial P beta

/--
[kwg_lowTempDualSum_sq_eq_kacWard_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_lowTempDualSum_sq_eq_kacWard_det_eq
  [Fintype V]
  [Fintype E]
  {P : PlanarZ2Subgraph}
  {beta : Real}
  {embedding : KWStraightLineEmbedding (kwg_subdivGraph (kwg_dualEnds P))} :
-- imply
  ((kwg_lowTempDualSum P beta : ℂ) ^ 2) = (1 - kwGraphTransition (kwg_subdivGraph (kwg_dualEnds P)) (kwg_subdivWeight (V := kwg_Face P) (fun _ => (Real.exp (-2 * beta) : ℂ))) embedding.turnPhase).det := by
-- proof
  apply StatMech.Onsager.kwg_lowTempDualSum_sq_eq_kacWard_det P beta embedding

/--
[ofReal_kwg_pathDefectSign_eq_prod_pathEdgeSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma ofReal_kwg_pathDefectSign_eq_prod_pathEdgeSign_eq
  [Fintype V]
  [Fintype E]
  {P : PlanarZ2Subgraph}
  {u v : P.V}
  {path : P.G.Walk u v}
  {F : Finset (kwg_Edge P)} :
-- imply
  (kwg_pathDefectSign P path F : ℂ) = ∏ e ∈ F, kwg_pathEdgeSign P path e := by
-- proof
  apply StatMech.Onsager.ofReal_kwg_pathDefectSign_eq_prod_pathEdgeSign P path F

/--
[ofReal_kwg_lowTempPathDualSum_eq_indexedEvenPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma ofReal_kwg_lowTempPathDualSum_eq_indexedEvenPolynomial_eq
  [Fintype V]
  [Fintype E]
  {P : PlanarZ2Subgraph}
  {beta : Real}
  {u v : P.V}
  {path : P.G.Walk u v} :
-- imply
  (kwg_lowTempPathDualSum P beta path : ℂ) = kwg_indexedEvenPolynomial (kwg_dualEnds P) (fun e => kwg_pathEdgeSign P path e * (Real.exp (-2 * beta) : ℂ)) := by
-- proof
  apply StatMech.Onsager.ofReal_kwg_lowTempPathDualSum_eq_indexedEvenPolynomial P beta path

/--
[kwg_lowTempPathDualSum_sq_eq_kacWard_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean)
-/
@[path]
private lemma kwg_lowTempPathDualSum_sq_eq_kacWard_det_eq
  [Fintype V]
  [Fintype E]
  {P : PlanarZ2Subgraph}
  {beta : Real}
  {u v : P.V}
  {path : P.G.Walk u v}
  {embedding : KWStraightLineEmbedding (kwg_subdivGraph (kwg_dualEnds P))} :
-- imply
  ((kwg_lowTempPathDualSum P beta path : ℂ) ^ 2) = (1 - kwGraphTransition (kwg_subdivGraph (kwg_dualEnds P)) (kwg_subdivWeight (V := kwg_Face P) (fun e => kwg_pathEdgeSign P path e * (Real.exp (-2 * beta) : ℂ))) embedding.turnPhase).det := by
-- proof
  apply StatMech.Onsager.kwg_lowTempPathDualSum_sq_eq_kacWard_det P beta path embedding


-- created on 2026-10-23
