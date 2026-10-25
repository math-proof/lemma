/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanCrossingCount.Part7
import Def.StatisticalMechanics.Code.Lattice.JordanWindingClose
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jwc_shared_eval (f0 f1 g0 g1 : ℤ) :
    sharedPrimalEdge ![f0, f1] ![g0, g1] =
      if f0 = g0 then
        s(![f0, max f1 g1], ![f0 + 1, max f1 g1])
      else
        s(![max f0 g0, f1], ![max f0 g0, f1 + 1]) := by
  unfold sharedPrimalEdge
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]


theorem jwc_shared_NE_NW (c d : ℤ) :
    sharedPrimalEdge ![c, d] ![c - 1, d] = s(![c, d], ![c, d + 1]) := by
  rw [jwc_shared_eval, if_neg (by omega)]
  rw [show max c (c - 1) = c by omega, Sym2.eq_iff]; tauto


theorem jwc_shared_NW_SW (c d : ℤ) :
    sharedPrimalEdge ![c - 1, d] ![c - 1, d - 1] = s(![c - 1, d], ![c, d]) := by
  rw [jwc_shared_eval, if_pos rfl]
  rw [show max d (d - 1) = d by omega, Sym2.eq_iff]
  left; refine ⟨rfl, ?_⟩; funext i; fin_cases i <;> simp


theorem jwc_shared_SW_SE (c d : ℤ) :
    sharedPrimalEdge ![c - 1, d - 1] ![c, d - 1] = s(![c, d - 1], ![c, d]) := by
  rw [jwc_shared_eval, if_neg (by omega)]
  rw [show max (c - 1) c = c by omega, Sym2.eq_iff]
  left; refine ⟨rfl, ?_⟩; funext i; fin_cases i <;> simp


theorem jwc_shared_SE_NE (c d : ℤ) :
    sharedPrimalEdge ![c, d - 1] ![c, d] = s(![c, d], ![c + 1, d]) := by
  rw [jwc_shared_eval, if_pos rfl]
  rw [show max (d - 1) d = d by omega, Sym2.eq_iff]; tauto


theorem jwc_vertexLoop_flipCount (E : Finset (Sym2 (Site 2))) (c d : ℤ) :
    wcl_flipCount (jce_edgeFlip E) (jwc_vertexLoop c d) =
      (if s(![c, d], ![c, d + 1]) ∈ E then 1 else 0)
    + ((if s(![c - 1, d], ![c, d]) ∈ E then 1 else 0)
    + ((if s(![c, d - 1], ![c, d]) ∈ E then 1 else 0)
    + ((if s(![c, d], ![c + 1, d]) ∈ E then 1 else 0) + 0))) := by
  classical
  unfold jwc_vertexLoop
  rw [wcl_flipCount_cons, wcl_flipCount_cons, wcl_flipCount_cons, wcl_flipCount_cons,
    wcl_flipCount_nil]
  
  
  
  have hcollapse : ∀ (a b : Site 2), (hypercubicLattice 2).Adj a b →
      ((jce_edgeFlip E a b ∨ jce_edgeFlip E b a) ↔ sharedPrimalEdge a b ∈ E) := by
    intro a b hab
    unfold jce_edgeFlip
    rw [sharedPrimalEdge_comm_of_adj hab, or_self]
  have e1 := hcollapse _ _ (jwc_faceAdj_NE_NW c d)
  have e2 := hcollapse _ _ (jwc_faceAdj_NW_SW c d)
  have e3 := hcollapse _ _ (jwc_faceAdj_SW_SE c d)
  have e4 := hcollapse _ _ (jwc_faceAdj_SE_NE c d)
  rw [jwc_shared_NE_NW] at e1
  rw [jwc_shared_NW_SW] at e2
  rw [jwc_shared_SW_SE] at e3
  rw [jwc_shared_SE_NE] at e4
  rw [if_congr e1 rfl rfl, if_congr e2 rfl rfl, if_congr e3 rfl rfl, if_congr e4 rfl rfl]


theorem jwc_jce_degree_eq (E : Finset (Sym2 (Site 2))) (c d : ℤ) :
    jce_degree (E : Set (Sym2 (Site 2))) ![c, d] =
      (if s(![c, d], ![c, d + 1]) ∈ E then 1 else 0)
    + ((if s(![c - 1, d], ![c, d]) ∈ E then 1 else 0)
    + ((if s(![c, d - 1], ![c, d]) ∈ E then 1 else 0)
    + ((if s(![c, d], ![c + 1, d]) ∈ E then 1 else 0) + 0))) := by
  classical
  unfold jce_degree jce_nbr
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Finset.mem_coe]
  rw [Finset.card_filter, Fin.sum_univ_four]
  
  rw [show s((![c, d] : Site 2), ![c - 1, d]) = s((![c - 1, d] : Site 2), ![c, d]) from Sym2.eq_swap,
    show s((![c, d] : Site 2), ![c, d - 1]) = s((![c, d - 1] : Site 2), ![c, d]) from Sym2.eq_swap]
  ring


theorem jwc_vertexLoop_even_iff (E : Finset (Sym2 (Site 2))) (c d : ℤ) :
    Even (wcl_flipCount (jce_edgeFlip E) (jwc_vertexLoop c d)) ↔
      Even (jce_degree (E : Set (Sym2 (Site 2))) ![c, d]) := by
  rw [jwc_vertexLoop_flipCount, jwc_jce_degree_eq]


theorem jwc_closedContour_of_edgeFlip_closedEven (E : Finset (Sym2 (Site 2)))
    (hce : wcl_ClosedEven (jce_edgeFlip E)) : jce_ClosedContour (E : Set (Sym2 (Site 2))) := by
  intro v
  have hvform : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hvform]
  rw [← jwc_vertexLoop_even_iff E (v 0) (v 1)]
  exact hce (jwc_vertexLoop (v 0) (v 1))


theorem jwc_edgeFlip_closedEven_iff_closedContour (E : Finset (Sym2 (Site 2))) :
    wcl_ClosedEven (jce_edgeFlip E) ↔ jce_ClosedContour (E : Set (Sym2 (Site 2))) := by
  constructor
  · exact jwc_closedContour_of_edgeFlip_closedEven E
  · exact jce_edgeFlip_closedEven jce_horizStepResidue_holds E


theorem jwc_cutFlip_closedEven_iff_closedContour (H : SimpleGraph (Site 2)) [Fintype H.edgeSet]
    (f0 g0 : Site 2) (hfg : (hypercubicLattice 2).Adj f0 g0) :
    wcl_ClosedEven (wcl_cutFlip H f0 g0) ↔
      jce_ClosedContour
        ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2)))
          : Set (Sym2 (Site 2))) := by
  set E := insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset with hE
  have hagree : ∀ a b, (hypercubicLattice 2).Adj a b →
      (wcl_cutFlip H f0 g0 a b ↔ jce_edgeFlip E a b) :=
    fun a b hab => jce_cutFlip_eq_edgeFlip H f0 g0 hfg hab
  constructor
  · intro hce
    apply (jwc_edgeFlip_closedEven_iff_closedContour E).mp
    exact jce_closedEven_congr (jce_edgeFlip E) (wcl_cutFlip H f0 g0)
      (fun a b hab => (hagree a b hab).symm) hce
  · intro hcc
    exact jce_closedEven_congr (wcl_cutFlip H f0 g0) (jce_edgeFlip E) hagree
      ((jwc_edgeFlip_closedEven_iff_closedContour E).mpr hcc)


theorem jwc_separated_of_closedContour (H : SimpleGraph (Site 2)) [Fintype H.edgeSet]
    (f0 g0 : Site 2) (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2)))
        : Set (Sym2 (Site 2)))) :
    ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 :=
  wcl_deleted_separated_of_closedEven H hfg
    ((jwc_cutFlip_closedEven_iff_closedContour H f0 g0 hfg).mpr hcc)


theorem jwc_faithfulDiscreteJordan_of_evenPeelable (P : PlanarZ2Subgraph)
    (hpe : jcx_IsEvenPeelable P.G) : whc_FaithfulDiscreteJordan P :=
  jcx_faithfulDiscreteJordan P hpe


theorem jwc_faceRegion_antitone {G1 G2 : SimpleGraph (Site 2)} (h : G1 ≤ G2) :
    whb_faceRegion G2 ≤ whb_faceRegion G1 := by
  intro f g hfg
  rw [whb_faceRegion_adj] at hfg ⊢
  exact ⟨hfg.1, fun hmem => hfg.2 (SimpleGraph.edgeSet_mono h hmem)⟩


theorem jwc_deleted_antitone {G1 G2 : SimpleGraph (Site 2)} (h : G1 ≤ G2) (f0 g0 : Site 2) :
    (whb_faceRegion G2).deleteEdges {s(f0, g0)} ≤
      (whb_faceRegion G1).deleteEdges {s(f0, g0)} := by
  intro f g hfg
  rw [deleteEdges_adj] at hfg ⊢
  exact ⟨jwc_faceRegion_antitone h hfg.1, hfg.2⟩


theorem jwc_separated_mono {G1 G2 : SimpleGraph (Site 2)} (h : G1 ≤ G2) {f0 g0 : Site 2}
    (hsep : ¬ ((whb_faceRegion G1).deleteEdges {s(f0, g0)}).Reachable f0 g0) :
    ¬ ((whb_faceRegion G2).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
  intro hreach
  exact hsep (hreach.mono (jwc_deleted_antitone h f0 g0))


theorem jwc_syncMerge_of_closedContour (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKle : K ≤ P.G) {f0 g0 : Site 2}
    (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge f0 g0) (jei_pushGraph_edgeSet_finite P K).toFinset
        : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2)))) :
    ¬ ((whb_faceRegion (jei_pushGraph P K)).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
  classical
  haveI := jfc_pushGraph_locallyFinite P K hKle
  haveI hft : Fintype (jei_pushGraph P K).edgeSet := (jei_pushGraph_edgeSet_finite P K).fintype
  have htoFinset : @Set.toFinset _ (jei_pushGraph P K).edgeSet hft
      = (jei_pushGraph_edgeSet_finite P K).toFinset := by
    apply Finset.ext; intro e
    rw [Set.mem_toFinset, Set.Finite.mem_toFinset]
  rw [← htoFinset] at hcc
  exact jwc_separated_of_closedContour (jei_pushGraph P K) f0 g0 hfg hcc


theorem jwc_pushGraph_mono (P : PlanarZ2Subgraph) {A B : SimpleGraph P.V} (h : A ≤ B) :
    jei_pushGraph P A ≤ jei_pushGraph P B := by
  rintro a b ⟨x, y, hxy, hx, hy⟩
  exact ⟨x, y, h hxy, hx, hy⟩


end Lattice
end StatMech
