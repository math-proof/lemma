/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part7
open Finset


namespace StatMech.FrontierD

theorem sixVertexHalfFilledRow_upCount (r : ℕ) :
    #{i | sixVertexHalfFilledRow r i} = r / 2 := by
  simp [sixVertexHalfFilledRow, Fin.card_filter_val_lt,
    Nat.div_le_self]


theorem sixVertexStraightExtendedToroidalBoundary_balanced
    {N M r : ℕ} (hN : Even N) (hr : Even r) (q : ℕ)
    (ξ : SixVertexToroidalBoundary N M) (hξ : ξ.Balanced) :
    (sixVertexStraightExtendedToroidalBoundary q ξ
      (sixVertexHalfFilledRow r)).Balanced := by
  unfold SixVertexToroidalBoundary.Balanced at hξ ⊢
  rw [Finset.card_filter, Fin.sum_univ_add]
  simp only [sixVertexStraightExtendedToroidalBoundary, Fin.addCases_left,
    Fin.addCases_right]
  rw [← Finset.card_filter, ← Finset.card_filter, hξ,
    sixVertexHalfFilledRow_upCount]
  rcases hN with ⟨N, rfl⟩
  rcases hr with ⟨r, rfl⟩
  have hNhalf : (N + N) / 2 = N := by omega
  have hrhalf : (r + r) / 2 = r := by omega
  rw [hNhalf, hrhalf]
  have hadd : (N + N) + (r + r) = (N + r) + (N + r) := by omega
  rw [hadd]
  omega


theorem sixVertexRectangleStraightExtend_injective
    {N M r q : ℕ} (z : Fin r → Bool) :
    Function.Injective
      (sixVertexRectangleStraightExtend (N := N + 1) (M := M + 1)
        (q := q) z) := by
  intro ω η h
  apply SixVertexRectangleArrows.ext
  · funext kj
    rcases kj with ⟨k, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) k
    · have h' := congrArg (fun ρ => ρ.horizontal
          (Fin.natAdd (N + 1) (0 : Fin (r + 1)), Fin.castAdd q j)) h
      simpa [sixVertexRectangleStraightExtend] using h'
    · have h' := congrArg (fun ρ => ρ.horizontal
          (Fin.castAdd (r + 1) i, Fin.castAdd q j)) h
      simpa [sixVertexRectangleStraightExtend] using h'
  · funext ik
    rcases ik with ⟨i, k⟩
    refine Fin.lastCases ?_ (fun j => ?_) k
    · have h' := congrArg (fun ρ => ρ.vertical
          (Fin.castAdd r i, Fin.natAdd (M + 1) (0 : Fin (q + 1)))) h
      simpa [sixVertexRectangleStraightExtend] using h'
    · have h' := congrArg (fun ρ => ρ.vertical
          (Fin.castAdd r i, Fin.castAdd (q + 1) j)) h
      simpa [sixVertexRectangleStraightExtend] using h'


end StatMech.FrontierD
