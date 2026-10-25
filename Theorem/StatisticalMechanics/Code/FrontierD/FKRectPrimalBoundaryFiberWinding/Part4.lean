/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleMergeWinding
import Theorem.StatisticalMechanics.Code.FrontierD.PermCycleQuotientWeightSum
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryFiberWinding.Part3
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectPrimalClusterBoundaryCycleWindingSum_eq_weightSum
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) :
    fkRectPrimalClusterBoundaryCycleWindingSum R omega x =
      fkRectPrimalClusterBoundaryWeightSum R omega x := by
  classical
  let sigma := fkMedialBlackBoundaryPerm
    (fkRectConfigurationToMedialPairing R omega)
  let p : FKMedialBlackDart R.medialTorus → Prop := fun d =>
    (fkRectOpenGraph R omega).Reachable x
      (fkRectMedialDartPrimalLabel R d.1)
  let f : FKMedialBlackDart R.medialTorus → Int × Int :=
    fkRectBlackBoundaryWeight R
      (fkRectConfigurationToMedialPairing R omega)
  have hinv : ∀ d e, sigma.SameCycle d e → (p d ↔ p e) := by
    intro d e hde
    have hmedial :
        (fkMedialLoopGraph R.medialTorus
          (fkRectConfigurationToMedialPairing R omega)).Reachable d.1 e.1 :=
      (fkMedial_blackBoundary_sameCycle_iff_reachable
        (fkRectConfigurationToMedialPairing R omega) d e).mp hde
    have hprimal := fkRectMedial_reachable_primalLabel_reachable
      R omega hmedial
    exact ⟨fun h => h.trans hprimal, fun h => h.trans hprimal.symm⟩
  unfold fkRectPrimalClusterBoundaryCycleWindingSum
  rw [show (∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
        if fkRectBlackBoundaryCycleInPrimalCluster R omega x C then
          fkRectBlackBoundaryCycleWinding R omega C else 0) =
      ∑ C : StatMech.FrontierA.PermCycleClass sigma,
        permCycleQuotientWeightSum sigma C
          (fun d => if p d then f d else 0) by
    apply Finset.sum_congr rfl
    intro C _
    induction C using Quot.ind with
    | _ d =>
      simp only [fkRectBlackBoundaryCycleInPrimalCluster_mk,
        fkRectBlackBoundaryCycleWinding_mk]
      change (if p d then permCycleClassWeightSum sigma d f else 0) =
        permCycleQuotientWeightSum sigma (Quot.mk _ d)
          (fun e => if p e then f e else 0)
      rw [permCycleQuotientWeightSum_mk,
        permCycleClassWeightSum_filter_of_sameCycle_invariant
          sigma p f hinv d]
  ]
  rw [sum_permCycleQuotientWeightSum]
  rfl


theorem fkRectPrimalClusterBoundaryWeightSum_eq_zero
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) :
    fkRectPrimalClusterBoundaryWeightSum R omega x = 0 := by
  let f : FKMedialBlackDart R.medialTorus → Int × Int := fun d =>
    if (fkRectOpenGraph R omega).Reachable x
        (fkRectMedialDartPrimalLabel R d.1) then
      fkRectBlackBoundaryWeight R
        (fkRectConfigurationToMedialPairing R omega) d
    else 0
  let g : R.medialTorus.Vertex × Bool → Int × Int := fun vb =>
    f ((fkMedialBlackDartEquivVertexBool R.medialTorus).symm vb)
  have hequiv : (∑ d : FKMedialBlackDart R.medialTorus, f d) =
      ∑ vb : R.medialTorus.Vertex × Bool, g vb := by
    apply Fintype.sum_equiv
      (fkMedialBlackDartEquivVertexBool R.medialTorus)
    intro d
    change f d = g ((fkMedialBlackDartEquivVertexBool R.medialTorus) d)
    unfold g
    rw [(fkMedialBlackDartEquivVertexBool
      R.medialTorus).symm_apply_apply]
  have hprod : (∑ vb : R.medialTorus.Vertex × Bool, g vb) =
      ∑ v : R.medialTorus.Vertex, ∑ b : Bool, g (v, b) :=
    Fintype.sum_prod_type g
  unfold fkRectPrimalClusterBoundaryWeightSum
  change (∑ d : FKMedialBlackDart R.medialTorus, f d) = 0
  rw [hequiv, hprod]
  apply Finset.sum_eq_zero
  intro v _
  rw [Fintype.sum_bool]
  simp [g, f, fkMedialBlackDartEquivVertexBool]
  change (if (fkRectOpenGraph R omega).Reachable x
        (fkRectMedialDartPrimalLabel R (fkMedialBlackDart1 v).1) then
      fkRectBlackBoundaryWeight R
        (fkRectConfigurationToMedialPairing R omega)
        (fkMedialBlackDart1 v)
    else 0) +
    (if (fkRectOpenGraph R omega).Reachable x
        (fkRectMedialDartPrimalLabel R (fkMedialBlackDart0 v).1) then
      fkRectBlackBoundaryWeight R
        (fkRectConfigurationToMedialPairing R omega)
        (fkMedialBlackDart0 v)
    else 0) = 0
  by_cases hopen : omega (fkRectTorusMedialEdgeEquiv R v) = true
  · have h01 := fkRectBlackDart01_primalLabels_reachable_of_open
      R omega v hopen
    have hiff : (fkRectOpenGraph R omega).Reachable x
          (fkRectMedialDartPrimalLabel R (fkMedialBlackDart0 v).1) ↔
        (fkRectOpenGraph R omega).Reachable x
          (fkRectMedialDartPrimalLabel R (fkMedialBlackDart1 v).1) :=
      ⟨fun h => h.trans h01, fun h => h.trans h01.symm⟩
    by_cases h0 : (fkRectOpenGraph R omega).Reachable x
        (fkRectMedialDartPrimalLabel R (fkMedialBlackDart0 v).1)
    · rw [if_pos h0, if_pos (hiff.mp h0)]
      simpa [add_comm] using
        fkRectBlackBoundaryWeight_dart0_add_dart1_eq_zero R omega v
    · rw [if_neg h0, if_neg (mt hiff.mpr h0), zero_add]
  · have hclosed : omega (fkRectTorusMedialEdgeEquiv R v) = false := by
      cases h : omega (fkRectTorusMedialEdgeEquiv R v)
      · rfl
      · exact absurd h hopen
    rw [fkRectBlackBoundaryWeight_dart0_eq_zero_of_closed R omega v hclosed,
      fkRectBlackBoundaryWeight_dart1_eq_zero_of_closed R omega v hclosed]
    simp


theorem fkRectPrimalClusterBoundaryCycleWindingSum_eq_zero
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) :
    fkRectPrimalClusterBoundaryCycleWindingSum R omega x = 0 := by
  rw [fkRectPrimalClusterBoundaryCycleWindingSum_eq_weightSum,
    fkRectPrimalClusterBoundaryWeightSum_eq_zero]


end
end StatMech.FrontierD
