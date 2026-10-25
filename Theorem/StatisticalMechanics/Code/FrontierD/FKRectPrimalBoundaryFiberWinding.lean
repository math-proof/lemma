/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleMergeWinding
import Theorem.StatisticalMechanics.Code.FrontierD.PermCycleQuotientWeightSum
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectBlackDart01_primalLabels
    (R : FKRectTorus) (v : R.medialTorus.Vertex) :
    s(fkRectMedialDartPrimalLabel R (fkMedialBlackDart0 v).1,
        fkRectMedialDartPrimalLabel R (fkMedialBlackDart1 v).1) =
      fkRectTorusIndexedEdge R (fkRectTorusMedialEdgeEquiv R v) := by
  let e := fkRectTorusMedialEdgeEquiv R v
  have hv : v = fkRectMedialVertexOfEdge R e :=
    ((fkRectTorusMedialEdgeEquiv R).symm_apply_apply v).symm
  rw [hv]
  rcases e with ⟨b, x, y⟩
  have hx : ¬ Even (1 + 2 * x.val) := by
    exact Nat.not_even_iff_odd.mpr ⟨x.val, by omega⟩
  cases b <;> by_cases hy : Even y.val <;>
    simp [fkMedialBlackDart0, fkMedialBlackDart1,
      fkRectMedialDartPrimalLabel, fkRectMedialWestPrimal,
      fkRectMedialEastPrimal, fkRectTorusIndexedEdge,
      fkRectClosedPairingAtEdge, fkMedialVertexParity, hy,
      hx, fkMedialCheckerColor, fkMedialSideVertical, Bool.toNat,
      Sym2.eq_swap]


theorem fkRectBlackDart01_primalLabels_reachable_of_open
    (R : FKRectTorus) (omega : R.Configuration)
    (v : R.medialTorus.Vertex)
    (hopen : omega (fkRectTorusMedialEdgeEquiv R v) = true) :
    (fkRectOpenGraph R omega).Reachable
      (fkRectMedialDartPrimalLabel R (fkMedialBlackDart0 v).1)
      (fkRectMedialDartPrimalLabel R (fkMedialBlackDart1 v).1) := by
  exact (show (fkRectOpenGraph R omega).Adj
      (fkRectMedialDartPrimalLabel R (fkMedialBlackDart0 v).1)
      (fkRectMedialDartPrimalLabel R (fkMedialBlackDart1 v).1) from
    ⟨fkRectTorusMedialEdgeEquiv R v, hopen,
      (fkRectBlackDart01_primalLabels R v).symm⟩).reachable


theorem fkRectBlackBoundaryWeight_dart0_add_dart1_eq_zero
    (R : FKRectTorus) (omega : R.Configuration)
    (v : R.medialTorus.Vertex) :
    fkRectBlackBoundaryWeight R
          (fkRectConfigurationToMedialPairing R omega)
          (fkMedialBlackDart0 v) +
        fkRectBlackBoundaryWeight R
          (fkRectConfigurationToMedialPairing R omega)
          (fkMedialBlackDart1 v) = 0 := by
  let F := fkRectOpenEdges R omega
  have homega : fkRectConfigurationOfEdges R F = omega :=
    fkRectConfigurationOfEdges_openEdges R omega
  let e := fkRectTorusMedialEdgeEquiv R v
  have hv : v = fkRectMedialVertexOfEdge R e :=
    ((fkRectTorusMedialEdgeEquiv R).symm_apply_apply v).symm
  rw [← homega, hv]
  by_cases heF : e ∈ F
  · let F0 := F.erase e
    have heF0 : e ∉ F0 := Finset.notMem_erase e F
    have hinsert : insert e F0 = F := Finset.insert_erase heF
    have hpair := fkRectBlackBoundaryWeight_toggle_pair_eq_zero
      R F0 e heF0
    rw [← fkRectConfigurationToMedialPairing_insert R F0 e heF0,
      hinsert] at hpair
    exact hpair
  · rw [fkRectBlackBoundaryWeight_closed_dart0_eq_zero R F e heF,
      fkRectBlackBoundaryWeight_closed_dart1_eq_zero R F e heF,
      zero_add]


theorem fkRectBlackBoundaryWeight_dart0_eq_zero_of_closed
    (R : FKRectTorus) (omega : R.Configuration)
    (v : R.medialTorus.Vertex)
    (hclosed : omega (fkRectTorusMedialEdgeEquiv R v) = false) :
    fkRectBlackBoundaryWeight R
        (fkRectConfigurationToMedialPairing R omega)
        (fkMedialBlackDart0 v) = 0 := by
  let F := fkRectOpenEdges R omega
  have homega : fkRectConfigurationOfEdges R F = omega :=
    fkRectConfigurationOfEdges_openEdges R omega
  let e := fkRectTorusMedialEdgeEquiv R v
  have hv : v = fkRectMedialVertexOfEdge R e :=
    ((fkRectTorusMedialEdgeEquiv R).symm_apply_apply v).symm
  have heF : e ∉ F := by
    intro he
    have hopen : fkRectConfigurationOfEdges R F e = true := by
      simp [fkRectConfigurationOfEdges, he]
    rw [homega, hclosed] at hopen
    contradiction
  rw [← homega, hv]
  exact fkRectBlackBoundaryWeight_closed_dart0_eq_zero R F e heF


theorem fkRectBlackBoundaryWeight_dart1_eq_zero_of_closed
    (R : FKRectTorus) (omega : R.Configuration)
    (v : R.medialTorus.Vertex)
    (hclosed : omega (fkRectTorusMedialEdgeEquiv R v) = false) :
    fkRectBlackBoundaryWeight R
        (fkRectConfigurationToMedialPairing R omega)
        (fkMedialBlackDart1 v) = 0 := by
  let F := fkRectOpenEdges R omega
  have homega : fkRectConfigurationOfEdges R F = omega :=
    fkRectConfigurationOfEdges_openEdges R omega
  let e := fkRectTorusMedialEdgeEquiv R v
  have hv : v = fkRectMedialVertexOfEdge R e :=
    ((fkRectTorusMedialEdgeEquiv R).symm_apply_apply v).symm
  have heF : e ∉ F := by
    intro he
    have hopen : fkRectConfigurationOfEdges R F e = true := by
      simp [fkRectConfigurationOfEdges, he]
    rw [homega, hclosed] at hopen
    contradiction
  rw [← homega, hv]
  exact fkRectBlackBoundaryWeight_closed_dart1_eq_zero R F e heF


end
end StatMech.FrontierD
