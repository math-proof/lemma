/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualLumpedLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualBundles.Part2
import Theorem.StatisticalMechanics.Code.FK.IndexedEdgeLumping.Part2
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualLumpedLaw.Part3
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

noncomputable section

theorem pfdDualWeight_openSub_eq_of_edges
    (P : PlanarZ2Subgraph) (p q : Real)
    (omega eta : ConfigSpace (Sym2 P.V))
    (h : ∀ e ∈ P.G.edgeFinset, omega e = eta e) :
    pfdDualWeight P p q (openSub P.G omega) =
      pfdDualWeight P p q (openSub P.G eta) := by
  rw [ecz_openSub_eq_of_edges P.G omega eta h]

theorem fkSquarePfdWeight_activeSplit
    (m : Nat) (p q : Real)
    (eta : ConfigSpace (FK.boxGraph 2 m).edgeSet)
    (xi : ConfigSpace {e : Sym2 (FK.boxVerts 2 m) //
      e ∉ (FK.boxGraph 2 m).edgeSet}) :
    pfdDualWeight (fkSquareBoxPlanar m) p q
        (openSub (FK.boxGraph 2 m)
          ((activeSplitEquiv (FK.boxGraph 2 m)).symm (eta, xi))) =
      pfdDualWeight (fkSquareBoxPlanar m) p q
        (openSub (FK.boxGraph 2 m)
          (extendActive (FK.boxGraph 2 m) eta)) := by
  apply pfdDualWeight_openSub_eq_of_edges
  intro e he
  have heSet : e ∈ (FK.boxGraph 2 m).edgeSet := by
    simpa only [SimpleGraph.mem_edgeFinset] using he
  have hsplit := congrFun
    (restrictActive_activeSplitEquiv_symm (FK.boxGraph 2 m) eta xi)
    ⟨e, heSet⟩
  calc
    ((activeSplitEquiv (FK.boxGraph 2 m)).symm (eta, xi)) e =
        eta ⟨e, heSet⟩ := hsplit
    _ = extendActive (FK.boxGraph 2 m) eta e := by
      symm
      exact extendActive_apply (FK.boxGraph 2 m) eta ⟨e, heSet⟩


theorem fkSquare_pfdDualNumer_eq_lumped
    {N m : Nat} (hNm : N < m) (p q : Real)
    (F : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet → Real) :
    (∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 m)),
      F (fkSquarePfdSupport m omega) *
        pfdDualWeight (fkSquareBoxPlanar m) p q
          (openSub (FK.boxGraph 2 m) omega)) =
      2 ^ ecz_NE (FK.boxGraph 2 m) *
        ∑ rho : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet,
          F rho * activeBCWeight (fkSquareBoxFullDualGraph m) ⊥
            (fkSquareDualLumpedParam N m p) q rho := by
  rw [← Equiv.sum_comp (activeSplitEquiv (FK.boxGraph 2 m)).symm,
    Fintype.sum_prod_type]
  have key : ∀ eta : ConfigSpace (FK.boxGraph 2 m).edgeSet,
      (∑ xi : ConfigSpace {e : Sym2 (FK.boxVerts 2 m) //
          e ∉ (FK.boxGraph 2 m).edgeSet},
        F (fkSquarePfdSupport m
          ((activeSplitEquiv (FK.boxGraph 2 m)).symm (eta, xi))) *
        pfdDualWeight (fkSquareBoxPlanar m) p q
          (openSub (FK.boxGraph 2 m)
            ((activeSplitEquiv (FK.boxGraph 2 m)).symm (eta, xi)))) =
        2 ^ ecz_NE (FK.boxGraph 2 m) *
          (F (pfdIndexedSupportActive (fkSquareBoxPlanar m)
              (pfdEdgeComplement (fkSquareBoxPlanar m) eta)) *
            pfdDualWeight (fkSquareBoxPlanar m) p q
              (openSub (FK.boxGraph 2 m)
                (extendActive (FK.boxGraph 2 m) eta))) := by
    intro eta
    rw [Finset.sum_congr rfl (fun xi _ => by
      simp only [fkSquarePfdSupport]
      rw [restrictActive_activeSplitEquiv_symm,
        fkSquarePfdWeight_activeSplit])]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      card_inactive_config (FK.boxGraph 2 m)]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun eta _ => key eta), ← Finset.mul_sum]
  congr 1
  have hreindex :
      (∑ i : ConfigSpace (fkSquareBoxPlanar m).G.edgeSet,
        F (pfdIndexedSupportActive (fkSquareBoxPlanar m)
            (pfdEdgeComplement (fkSquareBoxPlanar m) i)) *
          pfdDualWeight (fkSquareBoxPlanar m) p q
            (openSub (FK.boxGraph 2 m)
              (extendActive (FK.boxGraph 2 m) i))) =
        ∑ eta : ConfigSpace (fkSquareBoxPlanar m).G.edgeSet,
          F (pfdIndexedSupportActive (fkSquareBoxPlanar m) eta) *
            pfdDualWeight (fkSquareBoxPlanar m) p q
              (openSub (FK.boxGraph 2 m)
                (extendActive (FK.boxGraph 2 m)
                  (pfdEdgeComplement (fkSquareBoxPlanar m) eta))) := by
    let g := fun eta : ConfigSpace (fkSquareBoxPlanar m).G.edgeSet =>
      F (pfdIndexedSupportActive (fkSquareBoxPlanar m) eta) *
        pfdDualWeight (fkSquareBoxPlanar m) p q
          (openSub (FK.boxGraph 2 m)
            (extendActive (FK.boxGraph 2 m)
              (pfdEdgeComplement (fkSquareBoxPlanar m) eta)))
    simpa only [g, pfdEdgeComplement_involutive] using
      (Equiv.sum_comp (pfdEdgeComplement (fkSquareBoxPlanar m)) g)
  have hpoint : ∀ eta : ConfigSpace (fkSquareBoxPlanar m).G.edgeSet,
      pfdDualWeight (fkSquareBoxPlanar m) p q
          (openSub (FK.boxGraph 2 m)
            (extendActive (FK.boxGraph 2 m)
              (pfdEdgeComplement (fkSquareBoxPlanar m) eta))) =
        indexedBernoulliWeight p eta *
          q ^ numClustersBC (fkSquareBoxFullDualGraph m) ⊥
            (extendActive (fkSquareBoxFullDualGraph m)
              (pfdIndexedSupportActive (fkSquareBoxPlanar m) eta)) := by
    intro eta
    change pfdDualWeight (fkSquareBoxPlanar m) p q
        (openSub (fkSquareBoxPlanar m).G
          (extendActive (fkSquareBoxPlanar m).G
            (pfdEdgeComplement (fkSquareBoxPlanar m) eta))) = _
    rw [pfdDualWeight_eq_indexedSupport]
    have hcomp :
        (fun e : kwg_Edge (fkSquareBoxPlanar m) =>
          !(extendActive (fkSquareBoxPlanar m).G
            (pfdEdgeComplement (fkSquareBoxPlanar m) eta) e.1)) = eta := by
      funext e
      rw [extendActive_apply, pfdEdgeComplement_apply]
      simp
    rw [hcomp]
    unfold fkSquareBoxFullDualGraph
    rfl
  refine hreindex.trans ?_
  rw [Finset.sum_congr rfl (fun eta _ => by rw [hpoint eta])]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    pfdIndexedWeight_lumping hNm p q F


theorem fkSquare_pfdDualZ_eq_lumped
    {N m : Nat} (hNm : N < m) (p q : Real) :
    pfdDualZ (fkSquareBoxPlanar m) p q =
      2 ^ ecz_NE (FK.boxGraph 2 m) *
        activeBCZ (fkSquareBoxFullDualGraph m) ⊥
          (fkSquareDualLumpedParam N m p) q := by
  unfold pfdDualZ activeBCZ
  simpa using fkSquare_pfdDualNumer_eq_lumped hNm p q (fun _ => 1)


theorem fkSquare_pfdDualMean_eq_lumped
    {N m : Nat} (hNm : N < m) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet → Real) :
    (∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 m)),
      F (fkSquarePfdSupport m omega) *
        pfdDualProb (fkSquareBoxPlanar m) p q omega) =
      ∑ rho : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet,
        F rho * activeBCProb (fkSquareBoxFullDualGraph m) ⊥
          (fkSquareDualLumpedParam N m p) q rho := by
  unfold pfdDualProb activeBCProb
  change
    (∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 m)),
      F (fkSquarePfdSupport m omega) *
        (pfdDualWeight (fkSquareBoxPlanar m) p q
          (openSub (FK.boxGraph 2 m) omega) /
            pfdDualZ (fkSquareBoxPlanar m) p q)) =
      ∑ rho : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet,
        F rho * (activeBCWeight (fkSquareBoxFullDualGraph m) ⊥
          (fkSquareDualLumpedParam N m p) q rho /
            activeBCZ (fkSquareBoxFullDualGraph m) ⊥
              (fkSquareDualLumpedParam N m p) q)
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, ← Finset.sum_div,
    fkSquare_pfdDualNumer_eq_lumped hNm,
    fkSquare_pfdDualZ_eq_lumped hNm]
  have htwo : (2 : Real) ^ ecz_NE (FK.boxGraph 2 m) ≠ 0 := by positivity
  have hZ : activeBCZ (fkSquareBoxFullDualGraph m) ⊥
      (fkSquareDualLumpedParam N m p) q ≠ 0 :=
    (activeBCZ_pos _ _
      (fkSquareDualLumpedParam_pos hNm hp hp1)
      (fkSquareDualLumpedParam_lt_one hNm hp hp1) hq).ne'
  field_simp

end
end StatMech.FrontierD
