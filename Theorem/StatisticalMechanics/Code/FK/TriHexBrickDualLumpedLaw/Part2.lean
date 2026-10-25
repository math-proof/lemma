/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualLumpedLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickDualBundles
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualLumpedLaw.Part3
import Def.StatisticalMechanics.Code.FK.TriHexBrickDualLumpedLaw.Part2
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

open StatMech.FrontierD

noncomputable section

theorem triHexBrick_pfdDualWeight_openSub_eq_of_edges
    (P : PlanarZ2Subgraph) (p q : Real)
    (omega eta : ConfigSpace (Sym2 P.V))
    (h : ∀ e ∈ P.G.edgeFinset, omega e = eta e) :
    pfdDualWeight P p q (openSub P.G omega) =
      pfdDualWeight P p q (openSub P.G eta) := by
  rw [ecz_openSub_eq_of_edges P.G omega eta h]

theorem triHexBrickPfdWeight_activeSplit
    (m : Nat) (p q : Real)
    (eta : ConfigSpace (triHexPlanarFiniteStarPlanar m).G.edgeSet)
    (xi : ConfigSpace
      {e : Sym2 (triHexPlanarFiniteStarPlanar m).V //
        e ∉ (triHexPlanarFiniteStarPlanar m).G.edgeSet}) :
    pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
        (openSub (triHexPlanarFiniteStarPlanar m).G
          ((activeSplitEquiv (triHexPlanarFiniteStarPlanar m).G).symm
            (eta, xi))) =
      pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
        (openSub (triHexPlanarFiniteStarPlanar m).G
          (extendActive (triHexPlanarFiniteStarPlanar m).G eta)) := by
  apply triHexBrick_pfdDualWeight_openSub_eq_of_edges
  intro e he
  have heSet : e ∈ (triHexPlanarFiniteStarPlanar m).G.edgeSet := by
    simpa only [SimpleGraph.mem_edgeFinset] using he
  have hsplit := congrFun
    (restrictActive_activeSplitEquiv_symm
      (triHexPlanarFiniteStarPlanar m).G eta xi) ⟨e, heSet⟩
  calc
    ((activeSplitEquiv (triHexPlanarFiniteStarPlanar m).G).symm
        (eta, xi)) e = eta ⟨e, heSet⟩ := hsplit
    _ = extendActive (triHexPlanarFiniteStarPlanar m).G eta e := by
      symm
      exact extendActive_apply
        (triHexPlanarFiniteStarPlanar m).G eta ⟨e, heSet⟩


theorem triHexBrick_pfdDualNumer_eq_lumped
    {N m : Nat} (hNm : N < m) (p q : Real)
    (F : ConfigSpace (triHexBrickFullDualGraph m).edgeSet → Real) :
    (∑ omega : ConfigSpace
        (Sym2 (triHexPlanarFiniteStarPlanar m).V),
      F (triHexBrickPfdSupport m omega) *
        pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
          (openSub (triHexPlanarFiniteStarPlanar m).G omega)) =
      2 ^ ecz_NE (triHexPlanarFiniteStarPlanar m).G *
        ∑ rho : ConfigSpace (triHexBrickFullDualGraph m).edgeSet,
          F rho * activeBCWeight (triHexBrickFullDualGraph m) ⊥
            (triHexBrickDualLumpedParam N m p) q rho := by
  rw [← Equiv.sum_comp
      (activeSplitEquiv (triHexPlanarFiniteStarPlanar m).G).symm,
    Fintype.sum_prod_type]
  have key : ∀ eta : ConfigSpace
      (triHexPlanarFiniteStarPlanar m).G.edgeSet,
      (∑ xi : ConfigSpace
          {e : Sym2 (triHexPlanarFiniteStarPlanar m).V //
            e ∉ (triHexPlanarFiniteStarPlanar m).G.edgeSet},
        F (triHexBrickPfdSupport m
          ((activeSplitEquiv (triHexPlanarFiniteStarPlanar m).G).symm
            (eta, xi))) *
        pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
          (openSub (triHexPlanarFiniteStarPlanar m).G
            ((activeSplitEquiv (triHexPlanarFiniteStarPlanar m).G).symm
              (eta, xi)))) =
        2 ^ ecz_NE (triHexPlanarFiniteStarPlanar m).G *
          (F (pfdIndexedSupportActive
              (triHexPlanarFiniteStarPlanar m)
              (pfdEdgeComplement
                (triHexPlanarFiniteStarPlanar m) eta)) *
            pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
              (openSub (triHexPlanarFiniteStarPlanar m).G
                (extendActive (triHexPlanarFiniteStarPlanar m).G eta))) := by
    intro eta
    rw [Finset.sum_congr rfl (fun xi _ => by
      simp only [triHexBrickPfdSupport]
      rw [restrictActive_activeSplitEquiv_symm,
        triHexBrickPfdWeight_activeSplit])]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      card_inactive_config (triHexPlanarFiniteStarPlanar m).G]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun eta _ => key eta), ← Finset.mul_sum]
  congr 1
  have hreindex :
      (∑ i : ConfigSpace (triHexPlanarFiniteStarPlanar m).G.edgeSet,
        F (pfdIndexedSupportActive (triHexPlanarFiniteStarPlanar m)
            (pfdEdgeComplement (triHexPlanarFiniteStarPlanar m) i)) *
          pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
            (openSub (triHexPlanarFiniteStarPlanar m).G
              (extendActive (triHexPlanarFiniteStarPlanar m).G i))) =
        ∑ eta : ConfigSpace (triHexPlanarFiniteStarPlanar m).G.edgeSet,
          F (pfdIndexedSupportActive
              (triHexPlanarFiniteStarPlanar m) eta) *
            pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
              (openSub (triHexPlanarFiniteStarPlanar m).G
                (extendActive (triHexPlanarFiniteStarPlanar m).G
                  (pfdEdgeComplement
                    (triHexPlanarFiniteStarPlanar m) eta))) := by
    let g := fun eta : ConfigSpace
        (triHexPlanarFiniteStarPlanar m).G.edgeSet =>
      F (pfdIndexedSupportActive (triHexPlanarFiniteStarPlanar m) eta) *
        pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
          (openSub (triHexPlanarFiniteStarPlanar m).G
            (extendActive (triHexPlanarFiniteStarPlanar m).G
              (pfdEdgeComplement
                (triHexPlanarFiniteStarPlanar m) eta)))
    simpa only [g, pfdEdgeComplement_involutive] using
      (Equiv.sum_comp
        (pfdEdgeComplement (triHexPlanarFiniteStarPlanar m)) g)
  have hpoint : ∀ eta : ConfigSpace
      (triHexPlanarFiniteStarPlanar m).G.edgeSet,
      pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
          (openSub (triHexPlanarFiniteStarPlanar m).G
            (extendActive (triHexPlanarFiniteStarPlanar m).G
              (pfdEdgeComplement
                (triHexPlanarFiniteStarPlanar m) eta))) =
        indexedBernoulliWeight p eta *
          q ^ numClustersBC (triHexBrickFullDualGraph m) ⊥
            (extendActive (triHexBrickFullDualGraph m)
              (pfdIndexedSupportActive
                (triHexPlanarFiniteStarPlanar m) eta)) := by
    intro eta
    change pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
        (openSub (triHexPlanarFiniteStarPlanar m).G
          (extendActive (triHexPlanarFiniteStarPlanar m).G
            (pfdEdgeComplement
              (triHexPlanarFiniteStarPlanar m) eta))) = _
    rw [pfdDualWeight_eq_indexedSupport]
    have hcomp :
        (fun e : kwg_Edge (triHexPlanarFiniteStarPlanar m) =>
          !(extendActive (triHexPlanarFiniteStarPlanar m).G
            (pfdEdgeComplement (triHexPlanarFiniteStarPlanar m) eta)
              e.1)) = eta := by
      funext e
      rw [extendActive_apply, pfdEdgeComplement_apply]
      simp
    rw [hcomp]
    unfold triHexBrickFullDualGraph
    rfl
  refine hreindex.trans ?_
  rw [Finset.sum_congr rfl (fun eta _ => by rw [hpoint eta])]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    triHexBrick_pfdIndexedWeight_lumping hNm p q F


theorem triHexBrick_pfdDualZ_eq_lumped
    {N m : Nat} (hNm : N < m) (p q : Real) :
    pfdDualZ (triHexPlanarFiniteStarPlanar m) p q =
      2 ^ ecz_NE (triHexPlanarFiniteStarPlanar m).G *
        activeBCZ (triHexBrickFullDualGraph m) ⊥
          (triHexBrickDualLumpedParam N m p) q := by
  unfold pfdDualZ activeBCZ
  simpa using triHexBrick_pfdDualNumer_eq_lumped
    hNm p q (fun _ => 1)


theorem triHexBrick_pfdDualMean_eq_lumped
    {N m : Nat} (hNm : N < m) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : ConfigSpace (triHexBrickFullDualGraph m).edgeSet → Real) :
    (∑ omega : ConfigSpace
        (Sym2 (triHexPlanarFiniteStarPlanar m).V),
      F (triHexBrickPfdSupport m omega) *
        pfdDualProb (triHexPlanarFiniteStarPlanar m) p q omega) =
      ∑ rho : ConfigSpace (triHexBrickFullDualGraph m).edgeSet,
        F rho * activeBCProb (triHexBrickFullDualGraph m) ⊥
          (triHexBrickDualLumpedParam N m p) q rho := by
  unfold pfdDualProb activeBCProb
  change
    (∑ omega : ConfigSpace
        (Sym2 (triHexPlanarFiniteStarPlanar m).V),
      F (triHexBrickPfdSupport m omega) *
        (pfdDualWeight (triHexPlanarFiniteStarPlanar m) p q
          (openSub (triHexPlanarFiniteStarPlanar m).G omega) /
            pfdDualZ (triHexPlanarFiniteStarPlanar m) p q)) =
      ∑ rho : ConfigSpace (triHexBrickFullDualGraph m).edgeSet,
        F rho * (activeBCWeight (triHexBrickFullDualGraph m) ⊥
          (triHexBrickDualLumpedParam N m p) q rho /
            activeBCZ (triHexBrickFullDualGraph m) ⊥
              (triHexBrickDualLumpedParam N m p) q)
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, ← Finset.sum_div,
    triHexBrick_pfdDualNumer_eq_lumped hNm,
    triHexBrick_pfdDualZ_eq_lumped hNm]
  have htwo : (2 : Real) ^
      ecz_NE (triHexPlanarFiniteStarPlanar m).G ≠ 0 := by positivity
  have hZ : activeBCZ (triHexBrickFullDualGraph m) ⊥
      (triHexBrickDualLumpedParam N m p) q ≠ 0 :=
    (activeBCZ_pos _ _
      (triHexBrickDualLumpedParam_pos hNm hp hp1)
      (triHexBrickDualLumpedParam_lt_one hNm hp hp1) hq).ne'
  field_simp

end
end StatMech.FK.PeriodicPlanar
