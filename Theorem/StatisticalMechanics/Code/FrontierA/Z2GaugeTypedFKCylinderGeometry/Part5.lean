/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinder.Part4
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry.Part5
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

theorem cubicalLowerComplementInnerVertices_central_subset
    (n : Nat) :
    cubicalLowerComplementInnerVertices
        (a := centralSquareSide n) (b := centralSquareSide n)
        (c := centralSquareSide n + centralSquareSide n)
        (centralSquareSheetHeight n) ⊆
      centralLowerBoundaryVertices n := by
  intro v hv
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
  have hcut : p ∈ multibondCut
      (cubicalDualEnds
        (a := centralSquareSide n) (b := centralSquareSide n)
        (c := centralSquareSide n + centralSquareSide n))
      (cubicalBelowSpin (centralSquareSheetHeight n)) :=
    (Finset.mem_sdiff.mp hp).1
  have hnot : p ∉ cubicalXYSheet (centralSquareSheetHeight n) :=
    (Finset.mem_sdiff.mp hp).2
  have htrue := typedTrueEndpoint_spin_eq_true_of_mem_cut
    (cubicalDualEnds
      (a := centralSquareSide n) (b := centralSquareSide n)
      (c := centralSquareSide n + centralSquareSide n))
    (cubicalBelowSpin (centralSquareSheetHeight n)) p hcut
  rw [mem_multibondCut] at hcut
  cases p with
  | xy i j f =>
      cases hb : finBackward f with
      | none =>
          have hf0 : f = 0 := (finBackward_eq_none_iff f).mp hb
          subst f
          have hforward : finForward
              (0 : Fin (centralSquareSide n + centralSquareSide n + 1)) =
              some (centralBottomZ n) := by
            rw [finForward_eq_some_iff]
            apply Fin.ext
            rfl
          have hend : typedTrueEndpoint
              (cubicalDualEnds
                (a := centralSquareSide n) (b := centralSquareSide n)
                (c := centralSquareSide n + centralSquareSide n))
              (cubicalBelowSpin (centralSquareSheetHeight n))
              (CubicalPlaquette.xy i j 0) =
              some (CubicalCell.mk i j (centralBottomZ n)) := by
            simp [typedTrueEndpoint, cubicalDualEnds, hforward,
              hb, cubicalBelowSpin, centralBottomZ]
          rw [hend]
          simp [centralLowerBoundaryVertices, centralLowerBottomVertices]
      | some z =>
          cases hf : finForward f with
          | none =>
              simp [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                centralSquareSheetHeight] at hcut
              have hlast : f =
                  Fin.last (centralSquareSide n + centralSquareSide n) :=
                (finForward_eq_none_iff' f).mp hf
              have hsucc : f = z.succ :=
                (finBackward_eq_some_iff f z).mp hb
              have hzval : z.val + 1 =
                  centralSquareSide n + centralSquareSide n := by
                have := congrArg Fin.val (hsucc.symm.trans hlast)
                simpa using this
              simp [centralSquareSide] at hzval hcut
              omega
          | some w =>
              have hsucc : f = z.succ :=
                (finBackward_eq_some_iff f z).mp hb
              have hcast : f = w.castSucc :=
                (finForward_eq_some_iff f w).mp hf
              have hzw : w.val = z.val + 1 := by
                have := congrArg Fin.val (hsucc.symm.trans hcast)
                simpa using this.symm
              have hfval : f.val = z.val + 1 := by rw [hsucc]; simp
              simp [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                centralSquareSheetHeight] at hcut
              have hcenter : f = centralSquareSheetHeight n := by
                apply Fin.ext
                simp [centralSquareSheetHeight, centralSquareSide] at hfval ⊢
                omega
              apply False.elim
              apply hnot
              rw [hcenter]
              simp [cubicalXYSheet]
  | xz i f z =>
      cases hb : finBackward f with
      | none =>
          have hf0 : f = 0 := (finBackward_eq_none_iff f).mp hb
          subst f
          let y0 : Fin (centralSquareSide n) := 0
          have hforward : finForward
              (0 : Fin (centralSquareSide n + 1)) = some y0 := by
            rw [finForward_eq_some_iff]
            apply Fin.ext
            rfl
          have hz : z.val < centralSquareSide n := by
            simp [cubicalDualEnds, hforward, cubicalBelowSpin,
              hb, centralSquareSheetHeight, centralSquareSide] at hcut
            simpa [centralSquareSide] using hcut
          let zlow : Fin (centralSquareSide n) := ⟨z.val, hz⟩
          have hzcast : centralLowerZ zlow = z := by
            apply Fin.ext
            rfl
          have hend : typedTrueEndpoint cubicalDualEnds
              (cubicalBelowSpin (centralSquareSheetHeight n))
              (CubicalPlaquette.xz i
                (0 : Fin (centralSquareSide n + 1)) z) =
              some (CubicalCell.mk i
                (0 : Fin (centralSquareSide n)) z) := by
            simp [typedTrueEndpoint, cubicalDualEnds, hforward,
              hb, cubicalBelowSpin, y0]
          rw [hend]
          unfold centralLowerBoundaryVertices
          apply Finset.mem_union_left (centralLowerNorthVertices n)
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr
            ⟨(i, zlow), Finset.mem_univ _, by simp [hzcast]⟩
      | some y =>
          cases hf : finForward f with
          | none =>
              have hyLast : y = Fin.last n := by
                have hflast : f = Fin.last (centralSquareSide n) :=
                  (finForward_eq_none_iff' f).mp hf
                have hsucc : f = y.succ :=
                  (finBackward_eq_some_iff f y).mp hb
                apply Fin.ext
                have := congrArg Fin.val (hsucc.symm.trans hflast)
                simp [centralSquareSide] at this ⊢
                omega
              subst y
              have hz : z.val < centralSquareSide n := by
                simp [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                  centralSquareSheetHeight, centralSquareSide] at hcut
                simpa [centralSquareSide] using hcut
              let zlow : Fin (centralSquareSide n) := ⟨z.val, hz⟩
              have hzcast : centralLowerZ zlow = z := by
                apply Fin.ext
                rfl
              have hend : typedTrueEndpoint cubicalDualEnds
                  (cubicalBelowSpin (centralSquareSheetHeight n))
                  (CubicalPlaquette.xz i f z) =
                  some (CubicalCell.mk i (Fin.last n) z) := by
                simp [typedTrueEndpoint, cubicalDualEnds, hb, hf,
                  cubicalBelowSpin, centralSquareSheetHeight,
                  centralSquareSide, hz]
              rw [hend]
              unfold centralLowerBoundaryVertices
              apply Finset.mem_union_right
              exact Finset.mem_image.mpr
                ⟨(i, zlow), Finset.mem_univ _, by simp [hzcast]⟩
          | some y' =>
              simp [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                centralSquareSheetHeight] at hcut
  | yz f j z =>
      cases hb : finBackward f with
      | none =>
          have hf0 : f = 0 := (finBackward_eq_none_iff f).mp hb
          subst f
          let x0 : Fin (centralSquareSide n) := 0
          have hforward : finForward
              (0 : Fin (centralSquareSide n + 1)) = some x0 := by
            rw [finForward_eq_some_iff]
            apply Fin.ext
            rfl
          have hz : z.val < centralSquareSide n := by
            simp [cubicalDualEnds, hforward, cubicalBelowSpin,
              hb, centralSquareSheetHeight, centralSquareSide] at hcut
            simpa [centralSquareSide] using hcut
          let zlow : Fin (centralSquareSide n) := ⟨z.val, hz⟩
          have hzcast : centralLowerZ zlow = z := by
            apply Fin.ext
            rfl
          have hend : typedTrueEndpoint cubicalDualEnds
              (cubicalBelowSpin (centralSquareSheetHeight n))
              (CubicalPlaquette.yz
                (0 : Fin (centralSquareSide n + 1)) j z) =
              some (CubicalCell.mk
                (0 : Fin (centralSquareSide n)) j z) := by
            simp [typedTrueEndpoint, cubicalDualEnds, hforward,
              hb, cubicalBelowSpin, x0]
          rw [hend]
          unfold centralLowerBoundaryVertices
          apply Finset.mem_union_left (centralLowerNorthVertices n)
          apply Finset.mem_union_left (centralLowerSouthVertices n)
          apply Finset.mem_union_left (centralLowerEastVertices n)
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr
            ⟨(j, zlow), Finset.mem_univ _, by simp [hzcast]⟩
      | some x =>
          cases hf : finForward f with
          | none =>
              have hxLast : x = Fin.last n := by
                have hflast : f = Fin.last (centralSquareSide n) :=
                  (finForward_eq_none_iff' f).mp hf
                have hsucc : f = x.succ :=
                  (finBackward_eq_some_iff f x).mp hb
                apply Fin.ext
                have := congrArg Fin.val (hsucc.symm.trans hflast)
                simp [centralSquareSide] at this ⊢
                omega
              subst x
              have hz : z.val < centralSquareSide n := by
                simp [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                  centralSquareSheetHeight, centralSquareSide] at hcut
                simpa [centralSquareSide] using hcut
              let zlow : Fin (centralSquareSide n) := ⟨z.val, hz⟩
              have hzcast : centralLowerZ zlow = z := by
                apply Fin.ext
                rfl
              have hend : typedTrueEndpoint cubicalDualEnds
                  (cubicalBelowSpin (centralSquareSheetHeight n))
                  (CubicalPlaquette.yz f j z) =
                  some (CubicalCell.mk (Fin.last n) j z) := by
                simp [typedTrueEndpoint, cubicalDualEnds, hb, hf,
                  cubicalBelowSpin, centralSquareSheetHeight,
                  centralSquareSide, hz]
              rw [hend]
              unfold centralLowerBoundaryVertices
              apply Finset.mem_union_left (centralLowerNorthVertices n)
              apply Finset.mem_union_left (centralLowerSouthVertices n)
              apply Finset.mem_union_right
              exact Finset.mem_image.mpr
                ⟨(j, zlow), Finset.mem_univ _, by simp [hzcast]⟩
          | some x' =>
              simp [cubicalDualEnds, hb, hf, cubicalBelowSpin,
                centralSquareSheetHeight] at hcut


end
end StatMech.FrontierA
