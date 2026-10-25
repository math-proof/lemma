/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part12


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismFullTiltedTransitionProduct_positiveSplit
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real)
    (p : (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) ×
      (Fin (n - 1 + 1) ->
        RectangularLayerConfig (2 * n + 1) (2 * n + 1))) :
    oddPrismFullTiltedTransitionProduct beta n r
        (oddPrismPositiveSplitLayerPathConfigEquiv n hn p) =
      (∏ j : Fin n, rectangularPrismTransfer 1 beta
          (2 * n + 1) (2 * n + 1) (p.1 j.castSucc) (p.1 j.succ)) *
        oddPrismTiltedSeamTransfer beta n r
          (p.1 (Fin.last n)) (p.2 (Fin.last (n - 1))) *
        ∏ j : Fin (n - 1), rectangularPrismTransfer 1 beta
          (2 * n + 1) (2 * n + 1) (p.2 j.castSucc) (p.2 j.succ) := by
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let B := oddPrismTiltedSeamTransfer beta n r
  let sigma := oddPrismPositiveSplitLayerPathConfigEquiv n hn p
  change (∏ z : Fin (2 * n), if z.val = n then
      B (rectangularPrismLayer sigma z.castSucc)
        (rectangularPrismLayer sigma z.succ)
    else A (rectangularPrismLayer sigma z.castSucc)
        (rectangularPrismLayer sigma z.succ)) = _
  let e : (Fin n ⊕ Fin n) ≃ Fin (2 * n) :=
    finSumFinEquiv.trans (finCongr (by omega))
  rw [← e.prod_comp, Fintype.prod_sum_type]
  have hleft : (∏ j : Fin n,
      if (e (Sum.inl j)).val = n then
        B (rectangularPrismLayer sigma (e (Sum.inl j)).castSucc)
          (rectangularPrismLayer sigma (e (Sum.inl j)).succ)
      else A (rectangularPrismLayer sigma (e (Sum.inl j)).castSucc)
          (rectangularPrismLayer sigma (e (Sum.inl j)).succ)) =
      ∏ j : Fin n, A (p.1 j.castSucc) (p.1 j.succ) := by
    apply Fintype.prod_congr
    intro j
    have hj := j.isLt
    have he : e (Sum.inl j) = ⟨j.val, by omega⟩ := by
      apply Fin.ext
      simp [e]
    have hne : (e (Sum.inl j)).val ≠ n := by
      rw [he]
      exact Nat.ne_of_lt hj
    rw [if_neg hne, he]
    congr 2
    · exact rectangularPrismLayer_positiveSplitConfig_lower n hn p j.castSucc
    · exact rectangularPrismLayer_positiveSplitConfig_lower n hn p j.succ
  rw [hleft]
  let c : Fin (n - 1 + 1) ≃ Fin n := finCongr (by omega)
  have hright : (∏ k : Fin n,
      if (e (Sum.inr k)).val = n then
        B (rectangularPrismLayer sigma (e (Sum.inr k)).castSucc)
          (rectangularPrismLayer sigma (e (Sum.inr k)).succ)
      else A (rectangularPrismLayer sigma (e (Sum.inr k)).castSucc)
          (rectangularPrismLayer sigma (e (Sum.inr k)).succ)) =
      B (p.1 (Fin.last n)) (p.2 (Fin.last (n - 1))) *
        ∏ j : Fin (n - 1), A (p.2 j.castSucc) (p.2 j.succ) := by
    rw [← c.prod_comp, Fin.prod_univ_succ]
    congr 1
    · have hz : e (Sum.inr (c 0)) = ⟨n, by omega⟩ := by
        apply Fin.ext
        simp [e, c]
      rw [hz, if_pos rfl]
      congr 2
      · exact rectangularPrismLayer_positiveSplitConfig_lower n hn p
          (Fin.last n)
      · have hidx : (⟨n, by omega⟩ : Fin (2 * n)).succ =
            (⟨2 * n - (Fin.last (n - 1)).val, by omega⟩ :
              Fin (2 * n + 1)) := by
          apply Fin.ext
          simp
          omega
        rw [hidx]
        exact rectangularPrismLayer_positiveSplitConfig_upper n hn p
          (Fin.last (n - 1))
    · have hA : A.IsHermitian := rectangularPrismTransfer_isHermitian
          1 beta (2 * n + 1) (2 * n + 1)
      calc
        (∏ j : Fin (n - 1),
            if (e (Sum.inr (c j.succ))).val = n then
              B (rectangularPrismLayer sigma
                  (e (Sum.inr (c j.succ))).castSucc)
                (rectangularPrismLayer sigma (e (Sum.inr (c j.succ))).succ)
            else A (rectangularPrismLayer sigma
                  (e (Sum.inr (c j.succ))).castSucc)
                (rectangularPrismLayer sigma (e (Sum.inr (c j.succ))).succ)) =
            ∏ j : Fin (n - 1), A (p.2 (Fin.revPerm j).castSucc)
              (p.2 (Fin.revPerm j).succ) := by
          apply Fintype.prod_congr
          intro j
          let k := Fin.revPerm j
          have hz : e (Sum.inr (c j.succ)) =
              ⟨n + 1 + j.val, by omega⟩ := by
            apply Fin.ext
            simp [e, c]
            omega
          have hne : (e (Sum.inr (c j.succ))).val ≠ n := by
            rw [hz]
            change n + 1 + j.val ≠ n
            omega
          rw [if_neg hne, hz]
          have hidx1 :
              (⟨n + 1 + j.val, by omega⟩ : Fin (2 * n)).castSucc =
                (⟨2 * n - (k.succ).val, by omega⟩ : Fin (2 * n + 1)) := by
            apply Fin.ext
            simp [k, Fin.revPerm_apply]
            omega
          have hq1 : rectangularPrismLayer sigma
                (⟨n + 1 + j.val, by omega⟩ : Fin (2 * n)).castSucc =
              p.2 k.succ := by
            rw [hidx1]
            exact rectangularPrismLayer_positiveSplitConfig_upper n hn p k.succ
          have hidx2 : (⟨n + 1 + j.val, by omega⟩ : Fin (2 * n)).succ =
              (⟨2 * n - (k.castSucc).val, by omega⟩ : Fin (2 * n + 1)) := by
            apply Fin.ext
            simp [k, Fin.revPerm_apply]
            omega
          have hq2 : rectangularPrismLayer sigma
                (⟨n + 1 + j.val, by omega⟩ : Fin (2 * n)).succ =
              p.2 k.castSucc := by
            rw [hidx2]
            exact rectangularPrismLayer_positiveSplitConfig_upper n hn p k.castSucc
          rw [hq1, hq2]
          have hs := hA.apply (p.2 k.castSucc) (p.2 k.succ)
          simpa only [star_trivial] using hs
        _ = ∏ j : Fin (n - 1), A (p.2 j.castSucc) (p.2 j.succ) := by
          apply Fintype.prod_equiv Fin.revPerm
          intro j
          rfl
  rw [hright]
  ring


theorem oddPrismFullTiltedTransitionProduct_eq_ordinary_mul_exp
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    oddPrismFullTiltedTransitionProduct beta n r sigma =
      (∏ z : Fin (2 * n), rectangularPrismTransfer 1 beta
        (2 * n + 1) (2 * n + 1)
        (rectangularPrismLayer sigma z.castSucc)
        (rectangularPrismLayer sigma z.succ)) *
      Real.exp ((r - beta) * oddPrismFullSeamInteraction n sigma) := by
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let B := oddPrismTiltedSeamTransfer beta n r
  let z0 : Fin (2 * n) := ⟨n, by omega⟩
  let f : Fin (2 * n) -> Real := fun z =>
    A (rectangularPrismLayer sigma z.castSucc)
      (rectangularPrismLayer sigma z.succ)
  let g : Fin (2 * n) -> Real := fun z => if z.val = n then
    B (rectangularPrismLayer sigma z.castSucc)
      (rectangularPrismLayer sigma z.succ) else f z
  change (∏ z, g z) = (∏ z, f z) * _
  have hI : oddPrismFullSeamInteraction n sigma =
      oddPrismLayerSeamInteraction n
        (rectangularPrismLayer sigma z0.castSucc)
        (rectangularPrismLayer sigma z0.succ) := by
    rw [oddPrismFullSeamInteraction_eq_rectangularInterface n hn sigma,
      rectangularPrismInterfaceInteraction_eq_layerSeam n hn sigma]
    congr 1
  rw [hI]
  have hz0 : z0 ∈ (Finset.univ : Finset (Fin (2 * n))) := Finset.mem_univ _
  have hgErase : (∏ z ∈ (Finset.univ.erase z0), g z) =
      ∏ z ∈ (Finset.univ.erase z0), f z := by
    apply Finset.prod_congr rfl
    intro z hz
    have hne : z ≠ z0 := (Finset.mem_erase.mp hz).1
    have hval : z.val ≠ n := by
      intro hv
      apply hne
      apply Fin.ext
      exact hv
    simp [g, hval]
  calc
    (∏ z, g z) = g z0 * ∏ z ∈ (Finset.univ.erase z0), g z := by
      exact (Finset.mul_prod_erase Finset.univ g hz0).symm
    _ = B (rectangularPrismLayer sigma z0.castSucc)
          (rectangularPrismLayer sigma z0.succ) *
        ∏ z ∈ (Finset.univ.erase z0), f z := by
      rw [hgErase]
      congr 1
      simp [g, z0]
    _ = (A (rectangularPrismLayer sigma z0.castSucc)
          (rectangularPrismLayer sigma z0.succ) *
        Real.exp ((r - beta) * oddPrismLayerSeamInteraction n
          (rectangularPrismLayer sigma z0.castSucc)
          (rectangularPrismLayer sigma z0.succ))) *
        ∏ z ∈ (Finset.univ.erase z0), f z := by
      dsimp only [B, A]
      rw [oddPrismTiltedSeamTransfer_eq_transfer_mul_exp]
    _ = (A (rectangularPrismLayer sigma z0.castSucc)
          (rectangularPrismLayer sigma z0.succ) *
        ∏ z ∈ (Finset.univ.erase z0), f z) *
        Real.exp ((r - beta) * oddPrismLayerSeamInteraction n
          (rectangularPrismLayer sigma z0.castSucc)
          (rectangularPrismLayer sigma z0.succ)) := by ring
    _ = (∏ z, f z) *
        Real.exp ((r - beta) * oddPrismLayerSeamInteraction n
          (rectangularPrismLayer sigma z0.castSucc)
          (rectangularPrismLayer sigma z0.succ)) := by
      rw [Finset.mul_prod_erase Finset.univ f hz0]


end
end StatMech.FrontierA
