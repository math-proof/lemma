/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKInternalCylinder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry.Part8
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume.Part7
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKInternalCylinder.Part5
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem cubicalInternalCentralInnerVertices_subset_boundary
    (N m : Nat) (hN : 0 < N) (hNm : N < m) :
    cubicalInternalCentralInnerVertices N m hNm.le ⊆
      cubicalInternalCentralBoundaryVertices N m := by
  intro v hv
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
  have hcut : p ∈ multibondCut cubicalDualEnds
      (cubicalInternalCentralBlockSpin N m) :=
    (Finset.mem_sdiff.mp hp).1
  have hnot : p ∉ cubicalInternalCentralSheet N m hNm.le :=
    (Finset.mem_sdiff.mp hp).2
  have htrue := typedTrueEndpoint_spin_eq_true_of_mem_cut
    cubicalDualEnds (cubicalInternalCentralBlockSpin N m) p hcut
  cases hmark : typedTrueEndpoint cubicalDualEnds
      (cubicalInternalCentralBlockSpin N m) p with
  | none =>
      simp [cubicalInternalCentralBlockSpin, hmark] at htrue
  | some q =>
      have htrueQ : cubicalInternalCentralBlockSpin N m (some q) = true := by
        simpa [hmark] using htrue
      have hin :
          m <= q.x.val ∧ q.x.val < m + N ∧
          m <= q.y.val ∧ q.y.val < m + N ∧
          m - N <= q.z.val ∧ q.z.val < m := by
        simpa [cubicalInternalCentralBlockSpin] using htrueQ
      have hpCells : q ∈ cubicalPlaquetteCells p := by
        by_cases hchi : cubicalInternalCentralBlockSpin N m
            (cubicalDualEnds p).1 = true
        · have hfirst : (cubicalDualEnds p).1 = some q := by
            rw [← hmark]
            simp [typedTrueEndpoint, hchi]
          unfold cubicalPlaquetteCells
          rw [hfirst]
          simp
        · have hfalse : cubicalInternalCentralBlockSpin N m
              (cubicalDualEnds p).1 = false := by
            cases h : cubicalInternalCentralBlockSpin N m
                (cubicalDualEnds p).1
            · rfl
            · exact (hchi h).elim
          have hsecond : (cubicalDualEnds p).2 = some q := by
            rw [← hmark]
            simp [typedTrueEndpoint, hfalse]
          unfold cubicalPlaquetteCells
          rw [hsecond]
          simp
      have hpFace : p ∈ cubicalCellFaces q :=
        (mem_cubicalPlaquetteCells_iff_mem_cellFaces q p).mp hpCells
      apply Finset.mem_image.mpr
      refine ⟨q, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hin.1, hin.2.1, hin.2.2.1, hin.2.2.2.1,
        hin.2.2.2.2.1, hin.2.2.2.2.2, ?_⟩
      by_contra hboundary
      simp only [not_or] at hboundary
      rcases hboundary with ⟨hx0, hx1, hy0, hy1, hz0⟩
      simp only [cubicalCellFaces, Finset.mem_insert,
        Finset.mem_singleton] at hpFace
      rcases hpFace with hp | hp | hp | hp | hp | hp
      · subst p
        let prev : Fin (oddCubeSide m) :=
          ⟨q.z.val - 1, by dsimp [oddCubeSide]; omega⟩
        have hb : finBackward q.z.castSucc = some prev := by
          rw [finBackward_eq_some_iff]
          apply Fin.ext
          dsimp [prev]
          omega
        have hf : finForward q.z.castSucc = some q.z := by
          rw [finForward_eq_some_iff]
        rw [mem_multibondCut] at hcut
        simp only [cubicalDualEnds, hb, hf, Option.map_some] at hcut
        have hprev : cubicalInternalCentralBlockSpin N m
            (some (CubicalCell.mk q.x q.y prev)) = true := by
          simp [cubicalInternalCentralBlockSpin, prev]
          omega
        rw [hprev, htrueQ] at hcut
        exact hcut rfl
      · subst p
        let next : Fin (oddCubeSide m) :=
          ⟨q.z.val + 1, by dsimp [oddCubeSide]; omega⟩
        have hb : finBackward q.z.succ = some q.z := by
          rw [finBackward_eq_some_iff]
        have hf : finForward q.z.succ = some next := by
          rw [finForward_eq_some_iff]
          apply Fin.ext
          rfl
        rw [mem_cubicalInternalCentralSheet_iff] at hnot
        simp only [Fin.val_succ] at hnot
        rw [mem_multibondCut] at hcut
        simp only [cubicalDualEnds, hb, hf, Option.map_some] at hcut
        have hnext : cubicalInternalCentralBlockSpin N m
            (some (CubicalCell.mk q.x q.y next)) = true := by
          simp [cubicalInternalCentralBlockSpin, next]
          omega
        rw [htrueQ, hnext] at hcut
        exact hcut rfl
      · subst p
        let prev : Fin (oddCubeSide m) :=
          ⟨q.y.val - 1, by dsimp [oddCubeSide]; omega⟩
        have hb : finBackward q.y.castSucc = some prev := by
          rw [finBackward_eq_some_iff]
          apply Fin.ext
          dsimp [prev]
          omega
        have hf : finForward q.y.castSucc = some q.y := by
          rw [finForward_eq_some_iff]
        rw [mem_multibondCut] at hcut
        simp only [cubicalDualEnds, hb, hf, Option.map_some] at hcut
        have hprev : cubicalInternalCentralBlockSpin N m
            (some (CubicalCell.mk q.x prev q.z)) = true := by
          simp [cubicalInternalCentralBlockSpin, prev]
          omega
        rw [hprev, htrueQ] at hcut
        exact hcut rfl
      · subst p
        let next : Fin (oddCubeSide m) :=
          ⟨q.y.val + 1, by dsimp [oddCubeSide]; omega⟩
        have hb : finBackward q.y.succ = some q.y := by
          rw [finBackward_eq_some_iff]
        have hf : finForward q.y.succ = some next := by
          rw [finForward_eq_some_iff]
          apply Fin.ext
          rfl
        rw [mem_multibondCut] at hcut
        simp only [cubicalDualEnds, hb, hf, Option.map_some] at hcut
        have hnext : cubicalInternalCentralBlockSpin N m
            (some (CubicalCell.mk q.x next q.z)) = true := by
          simp [cubicalInternalCentralBlockSpin, next]
          omega
        rw [htrueQ, hnext] at hcut
        exact hcut rfl
      · subst p
        let prev : Fin (oddCubeSide m) :=
          ⟨q.x.val - 1, by dsimp [oddCubeSide]; omega⟩
        have hb : finBackward q.x.castSucc = some prev := by
          rw [finBackward_eq_some_iff]
          apply Fin.ext
          dsimp [prev]
          omega
        have hf : finForward q.x.castSucc = some q.x := by
          rw [finForward_eq_some_iff]
        rw [mem_multibondCut] at hcut
        simp only [cubicalDualEnds, hb, hf, Option.map_some] at hcut
        have hprev : cubicalInternalCentralBlockSpin N m
            (some (CubicalCell.mk prev q.y q.z)) = true := by
          simp [cubicalInternalCentralBlockSpin, prev]
          omega
        rw [hprev, htrueQ] at hcut
        exact hcut rfl
      · subst p
        let next : Fin (oddCubeSide m) :=
          ⟨q.x.val + 1, by dsimp [oddCubeSide]; omega⟩
        have hb : finBackward q.x.succ = some q.x := by
          rw [finBackward_eq_some_iff]
        have hf : finForward q.x.succ = some next := by
          rw [finForward_eq_some_iff]
          apply Fin.ext
          rfl
        rw [mem_multibondCut] at hcut
        simp only [cubicalDualEnds, hb, hf, Option.map_some] at hcut
        have hnext : cubicalInternalCentralBlockSpin N m
            (some (CubicalCell.mk next q.y q.z)) = true := by
          simp [cubicalInternalCentralBlockSpin, next]
          omega
        rw [htrueQ, hnext] at hcut
        exact hcut rfl


theorem cubicalInternalCentralDisconnections_subset_consistency
    (N m : Nat) (hN : 0 < N) (hNm : N <= m) :
    finiteEventInter
        ((cubicalInternalCentralInnerVertices N m hNm).product
          (cubicalInternalCentralUpperVertices N m hNm))
        (fun uv => typedFKDisconnEvent cubicalDualEnds uv.1 uv.2) ⊆
      typedFKConsistencyEvent cubicalDualEnds
        (cubicalInternalCentralSheet N m hNm) := by
  apply typedTwoCutMarkedDisconnections_subset_consistency
    cubicalDualEnds
    (cubicalDualEnds_ne
      (by simp [oddCubeSide]) (by simp [oddCubeSide])
      (by simp [oddCubeSide]))
    (cubicalInternalCentralSheet N m hNm)
    (cubicalInternalCentralComplement N m hNm)
    (cubicalInternalCentralSheet N m hNm)
    (cubicalInternalCentralBlockSpin N m)
    (cubicalInternalCentralBlockSpin N m)
  · exact internalCentralCut_eq_sheet_symmDiff_complement N m hN hNm
  · rw [Finset.union_comm]
    exact internalCentralCut_eq_sheet_union_complement N m hN hNm


theorem cubicalInternalCentral_consistencyMass_ge_product
    (N m : Nat) (hN : 0 < N) (hNm : N <= m)
    (J : CubicalPlaquette (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) -> Real)
    (hJ : forall p, 0 <= J p) :
    (∏ uv ∈ (cubicalInternalCentralInnerVertices N m hNm).product
        (cubicalInternalCentralUpperVertices N m hNm),
      (1 - multibondIsingTwoPoint cubicalDualEnds J uv.1 uv.2)) <=
      multibondIsingPartition cubicalDualEnds
          (multibondTwistCoupling J (cubicalInternalCentralSheet N m hNm)) /
        multibondIsingPartition cubicalDualEnds J := by
  apply multibondIsing_twist_ratio_ge_pair_correlation_product
    cubicalDualEnds J hJ (cubicalInternalCentralSheet N m hNm)
    (cubicalInternalCentralInnerVertices N m hNm)
    (cubicalInternalCentralUpperVertices N m hNm)
  exact cubicalInternalCentralDisconnections_subset_consistency N m hN hNm


theorem cubicalInternalCentralWilsonExpectation_ge_product
    (N m : Nat) (hN : 0 < N) (hNm : N <= m)
    (K : CubicalPlaquette (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) -> Real)
    (hK : forall p, 0 < K p) :
    (∏ uv ∈ (cubicalInternalCentralInnerVertices N m hNm).product
        (cubicalInternalCentralUpperVertices N m hNm),
      (1 - multibondIsingTwoPoint cubicalDualEnds
        (fun p => gaugeDualCoupling (K p)) uv.1 uv.2)) <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence K
        (gaugeSurfaceBoundary cubicalPlaquetteIncidence
          (cubicalInternalCentralSheet N m hNm)) := by
  rw [cubicalWilsonExpectation_eq_twistedIsingPartitionRatio_of_surface
    (by simp [oddCubeSide]) (by simp [oddCubeSide])
    (by simp [oddCubeSide]) K hK (cubicalInternalCentralSheet N m hNm)]
  exact cubicalInternalCentral_consistencyMass_ge_product N m hN hNm
    (fun p => gaugeDualCoupling (K p))
    (fun p => (gaugeDualCoupling_pos (hK p)).le)

end
end StatMech.FrontierA
