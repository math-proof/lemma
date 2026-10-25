/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedBoundaryGluing
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part6
open Finset Matrix


namespace StatMech.FrontierD

def svHorizontalIceEquivBool {N : Nat} (hN : 0 < N)
    (x y : SixVertexRow N) (hcount : sixVertexUpCount x = sixVertexUpCount y) :
    {h : SixVertexRow N // svHorizontalIce hN x y h} ≃
      {b : Bool // if b then svRowPrefixForward y x else svRowPrefixForward x y} where
  toFun h := by
    refine ⟨h.1 (svFinLast hN), ?_⟩
    obtain hcase | hcase := svHorizontalIce_cases hN h.2
    · rw [hcase.1]
      exact hcase.2.1
    · rw [hcase.1]
      exact hcase.2.1
  invFun b := ⟨svHorizontalOfBool x y b.1,
    svHorizontalOfBool_ice hN x y hcount b.1 b.2⟩
  left_inv h := by
    apply Subtype.ext
    obtain hcase | hcase := svHorizontalIce_cases hN h.2
    · rw [hcase.2.2]
      simp [svHorizontalOfBool, hcase.1]
    · rw [hcase.2.2]
      simp [svHorizontalOfBool, hcase.1]
  right_inv b := by
    apply Subtype.ext
    cases hb : b.1 with
    | false =>
        simpa [svHorizontalOfBool, hb] using
          svForwardHorizontal_last hN x y hcount
    | true =>
        simpa [svHorizontalOfBool, hb] using
          svBackwardHorizontal_last hN x y hcount

def svHorizontalIsC {N : Nat} (hN : 0 < N)
    (h : SixVertexRow N) (i : Fin N) : Prop :=
  (h (SixVertexArrows.cyclicPred hN i)).toNat + (!h i).toNat = 0 ∨
    (h (SixVertexArrows.cyclicPred hN i)).toNat + (!h i).toNat = 2

noncomputable def svHorizontalLocalWeight {N : Nat} (hN : 0 < N)
    (c : Real) (x y h : SixVertexRow N) (i : Fin N) : Real := by
  classical
  exact if svHorizontalIncomingCount hN x y h i = 2 then
    if svHorizontalIsC hN h i then c else 1
  else 0

noncomputable def svHorizontalRowWeight {N : Nat} (hN : 0 < N)
    (c : Real) (x y h : SixVertexRow N) : Real :=
  ∏ i, svHorizontalLocalWeight hN c x y h i

end StatMech.FrontierD
