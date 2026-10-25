/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFreeCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickDualCoordinates.Part4
import Theorem.StatisticalMechanics.Code.FK.FreeNestedDecreasing
import Def.StatisticalMechanics.Code.FK.TriHexBrickFreeCofinal
open Filter Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

open StatMech.FrontierD

noncomputable section

theorem triHexPlanarFiniteStarToHexBuffered_edgeIncl
    (m : Nat) (e : Sym2 (triHexPlanarFiniteStarPlanar m).V) :
    triHexPlanarFiniteStarEdgeIncl m e =
      hexagonal.edgeIncl (hexagonal.bufferedRadius (m + 2))
        (ocd_innerEdge (triHexPlanarFiniteStarToHexBuffered m) e) := by
  induction e using Sym2.inductionOn with
  | _ x y => rfl


theorem triHexFaceDualInnerActive_starRestrict_buffered
    {N m : Nat} (hNm : N < m)
    (rho : ConfigSpace (Sym2 (hexagonal.BufferedVertex (m + 2)))) :
    triHexFaceDualInnerActive N
        (triHexPlanarFiniteStarExtendEdge m
          (ocd_innerRestrict
            (triHexPlanarFiniteStarToHexBuffered m) rho)) =
      triHexFaceDualInnerActive N
        (hexagonal.extendEdge (hexagonal.bufferedRadius (m + 2)) rho) := by
  funext a
  rcases a with ⟨a, ha⟩
  induction a using Sym2.inductionOn with
  | _ x y =>
      have hxy : (triangularBoxGraph N).Adj x y :=
        (SimpleGraph.mem_edgeSet _).1 ha
      have hfull : (triHexBrickFullDualGraph m).Adj
          (triHexBrickInnerFaceMap N m x)
          (triHexBrickInnerFaceMap N m y) :=
        (triHexBrickInnerFaceMap_adj hNm x y).mp hxy
      obtain ⟨e, heBundle⟩ := pfdEdgeBundle_nonempty_of_fullDualEdge
        (triHexPlanarFiniteStarPlanar m)
        ((SimpleGraph.mem_edgeSet _).2 hfull)
      rw [mem_pfdEdgeBundle] at heBundle
      have heIncl :=
        triHexPlanarFiniteStar_edgeIncl_eq_fullDual_of_dualEnds_eq_inner
          hNm heBundle
      unfold triHexFaceDualInnerActive
      simp only [Sym2.map_mk]
      rw [← heIncl,
        triHexPlanarFiniteStarExtendEdge_edgeIncl,
        triHexPlanarFiniteStarToHexBuffered_edgeIncl,
        hexagonal.extendEdge_edgeIncl]
      rfl

theorem triHexStarFaceDualInnerEvent_preimage_outerBuffered
    {N m : Nat} (hNm : N < m)
    (A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)) :
    ocd_innerRestrict (triHexPlanarFiniteStarToHexBuffered m) ⁻¹'
        triHexStarFaceDualInnerEvent hNm A =
      triHexHexBufferedFaceDualInnerEvent N (m + 2) A := by
  ext rho
  change (triHexBrickDualInnerActiveRestrict hNm
      (triHexBrickPfdSupport m
        (ocd_innerRestrict
          (triHexPlanarFiniteStarToHexBuffered m) rho)) ∈ A ↔
    triHexFaceDualInnerActive N
      (hexagonal.extendEdge (hexagonal.bufferedRadius (m + 2)) rho) ∈ A)
  rw [triHexBrickDualInnerActiveRestrict_pfdSupport_eq_faceDual,
    triHexFaceDualInnerActive_starRestrict_buffered hNm]
  rfl

theorem triHexStarFaceDualInnerEvent_isDecreasing
    {N m : Nat} (hNm : N < m)
    {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
    (hA : IsIncreasing A) :
    IsDecreasing (triHexStarFaceDualInnerEvent hNm A) := by
  rw [show triHexStarFaceDualInnerEvent hNm A =
      triHexPlanarFiniteStarExtendEdge m ⁻¹'
        triHexFaceDualInnerEvent N A by
    ext omega
    simp only [triHexStarFaceDualInnerEvent,
      triHexFaceDualInnerEvent, Set.mem_setOf_eq, Set.mem_preimage]
    rw [triHexBrickDualInnerActiveRestrict_pfdSupport_eq_faceDual]
    rfl]
  intro eta omega home hmem
  apply (triHexFaceDualInnerEvent_isDecreasing N hA)
  · exact monotone_triHexPlanarFiniteStarExtendEdge m home
  · exact hmem


theorem triHexHexBufferedFaceDualInnerEvent_le_freeStar
    {N m : Nat} (hNm : N < m)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
    (hA : IsIncreasing A) :
    (∑ rho,
        (triHexHexBufferedFaceDualInnerEvent N (m + 2) A).indicator
          (fun _ => (1 : Real)) rho *
        fkProb (hexagonal.bufferedGraph (m + 2)) p q rho) ≤
      ∑ omega : ConfigSpace
          (Sym2 (TriHexPlanarFiniteStarVertex m)),
        (triHexStarFaceDualInnerEvent hNm A).indicator
          (fun _ => (1 : Real)) omega *
        fkProb (triHexPlanarFiniteStarGraph m) p q omega := by
  have hdom := bdp_free_outer_dominated_inner_decreasing
    (triHexPlanarFiniteStarToHexBuffered m).injective
    (triHexPlanarFiniteStarToHexBuffered_adjMatch m)
    hp hp1 hq (triHexStarFaceDualInnerEvent_isDecreasing hNm hA)
  rw [triHexStarFaceDualInnerEvent_preimage_outerBuffered hNm] at hdom
  exact hdom


end
end StatMech.FK.PeriodicPlanar
