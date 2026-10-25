/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffset.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedDensityPerron.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootOffsetAbstract
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOffset


namespace StatMech.FrontierD

open Finset

noncomputable section

theorem sixVertexCanonicalEvenHalfIndex_quantum
    (s k : Nat) (j : Fin ((s + k + 1) + (s + k + 1))) :
    sixVertexCentralQuantumNumber (sixVertexCanonicalEvenHalfIndex s k j) =
      sixVertexCentralQuantumNumber j := by
  rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
  simp only [sixVertexCanonicalEvenHalfIndex, Fin.val_mk]
  push_cast
  ring

theorem sixVertexCanonicalEvenChargeOffset_eq_thetaDifference
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexFixedEvenChargePerronBranchWitness c s k
      (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k))
    (j : Fin ((s + k + 1) + (s + k + 1))) :
    sixVertexCanonicalEvenChargeOffset hc s k j =
      (∑ l, sixVertexTheta c
          (sixVertexCanonicalEvenAlignedHalfRoots hc s k j)
          (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + k) l)) -
        ∑ l, sixVertexTheta c
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j)
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k l) := by
  let N := sixVertexFourWidth (2 * s) k
  let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + k)
  have hfixedEq := hfixed.2.1 j
  have hhalfEq :=
    sixVertexCanonicalDensityPerronBetheRoots_is_solution hc (2 * s + k)
      (sixVertexCanonicalEvenHalfIndex s k j)
  have hwidth : sixVertexFourWidth 0 (2 * s + k) = N := by
    dsimp [N]
    unfold sixVertexFourWidth
    omega
  rw [hwidth, sixVertexCanonicalEvenHalfIndex_quantum] at hhalfEq
  change (N : Real) * q j =
    2 * Real.pi * sixVertexCentralQuantumNumber j -
      ∑ l, sixVertexTheta c (q j) (q l) at hfixedEq
  change (N : Real) * p (sixVertexCanonicalEvenHalfIndex s k j) =
    2 * Real.pi * sixVertexCentralQuantumNumber j -
      ∑ l, sixVertexTheta c
        (p (sixVertexCanonicalEvenHalfIndex s k j)) (p l) at hhalfEq
  unfold sixVertexCanonicalEvenChargeOffset
    sixVertexCanonicalEvenAlignedHalfRoots
  linarith

theorem sixVertexCanonicalEvenChargeOffset_eq_boundary_add_commonDifference
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexFixedEvenChargePerronBranchWitness c s k
      (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k))
    (j : Fin ((s + k + 1) + (s + k + 1))) :
    sixVertexCanonicalEvenChargeOffset hc s k j =
      sixVertexCanonicalEvenOffsetBoundarySource hc s k j +
        ∑ l, (sixVertexTheta c
          (sixVertexCanonicalEvenAlignedHalfRoots hc s k j)
          (sixVertexCanonicalEvenAlignedHalfRoots hc s k l) -
        sixVertexTheta c
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j)
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k l)) := by
  rw [sixVertexCanonicalEvenChargeOffset_eq_thetaDifference hc s k hfixed j]
  unfold sixVertexCanonicalEvenOffsetBoundarySource
  rw [sum_sub_distrib]
  ring

theorem abs_sixVertexCanonicalEvenOffsetNodalResidual_le
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexFixedEvenChargePerronBranchWitness c s k
      (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k))
    {B : Real} (hB : 0 <= B)
    (hoffset : forall j, |sixVertexCanonicalEvenChargeOffset hc s k j| <= B)
    (j : Fin ((s + k + 1) + (s + k + 1))) :
    |sixVertexCanonicalEvenOffsetNodalResidual hc s k j| <=
      4 * sixVertexThetaTaylorBound c * B ^ 2 /
        sixVertexFourWidth (2 * s) k := by
  let N := sixVertexFourWidth (2 * s) k
  let p := sixVertexCanonicalEvenAlignedHalfRoots hc s k
  let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
  let eps := sixVertexCanonicalEvenChargeOffset hc s k
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s) k
  have hn : (s + k + 1) + (s + k + 1) <= N := by
    dsimp [N]
    unfold sixVertexFourWidth
    omega
  apply abs_genericOffsetNodalResidual_le hc hN hn hB
    (p := p) (q := q) (eps := eps)
    (boundary := sixVertexCanonicalEvenOffsetBoundarySource hc s k)
  · intro l
    rfl
  · exact hoffset
  · intro l
    have h := sixVertexCanonicalEvenChargeOffset_eq_boundary_add_commonDifference
      hc s k hfixed l
    change eps l - sixVertexCanonicalEvenOffsetBoundarySource hc s k l = _
    linarith

end
end StatMech.FrontierD
