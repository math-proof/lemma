/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianStability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheJacobianSign
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheJacobianStability.Part4
open Finset Filter Topology Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheSymmetricHalfJacobianMatrix_offdiag_nonneg
    {N m : Nat} {c : Real} (hc : 2 < c)
    {p : Fin (m + m) → Real} (hp : SixVertexOpenRootSimplex p)
    {j k : Fin m} (hjk : j ≠ k) :
    0 ≤ sixVertexBetheSymmetricHalfJacobianMatrix N m c p j k := by
  let i := sixVertexFirstHalfIndex m j
  let l := sixVertexFirstHalfIndex m k
  let lr := sixVertexReflectedHalfIndex m k
  have hil : i ≠ l := by
    intro h
    apply hjk
    have hval := congrArg Fin.val h
    dsimp [i, l, sixVertexFirstHalfIndex] at hval
    exact Fin.ext hval
  have hilr : i ≠ lr := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [i, lr, sixVertexFirstHalfIndex,
      sixVertexReflectedHalfIndex, Fin.rev] at hval
    omega
  have hsymm : p lr = -p l := by
    exact hp.2.1 l
  have hiIcc : p i ∈ Set.Icc (-Real.pi) 0 :=
    sixVertexFirstHalfRoot_mem_Icc hp j
  have hlIcc : p l ∈ Set.Icc (-Real.pi) 0 :=
    sixVertexFirstHalfRoot_mem_Icc hp k
  have hsign := sixVertexTheta_right_difference_nonneg hc hiIcc hlIcc
  unfold sixVertexBetheSymmetricHalfJacobianMatrix
  rw [sixVertexBetheJacobianMatrix, if_neg hil,
    sixVertexBetheJacobianMatrix, if_neg hilr, hsymm,
    sixVertexBetheIntegratingFactor]
  rw [sixVertexThetaDerivativeDenominator_neg_right]
  simpa [i, l, lr, sixVertexBetheIntegratingFactor, Real.cos_neg] using hsign

end
end StatMech.FrontierD
