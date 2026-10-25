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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheJacobianStability.Part3
open Finset Filter Topology Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFirstHalfIndex_lt_reflected (m : Nat) (j : Fin m) :
    sixVertexFirstHalfIndex m j < sixVertexReflectedHalfIndex m j := by
  rw [Fin.lt_def]
  simp [sixVertexFirstHalfIndex, sixVertexReflectedHalfIndex, Fin.rev]
  omega

theorem sixVertexFirstHalfRoot_mem_Icc
    {m : Nat} {p : Fin (m + m) → Real}
    (hp : SixVertexOpenRootSimplex p) (j : Fin m) :
    p (sixVertexFirstHalfIndex m j) ∈ Set.Icc (-Real.pi) 0 := by
  let i := sixVertexFirstHalfIndex m j
  have hlt := hp.1 (sixVertexFirstHalfIndex_lt_reflected m j)
  have hsymm := hp.2.1 i
  have hneg : p i < 0 := by
    change p i < p i.rev at hlt
    rw [hsymm] at hlt
    linarith
  exact ⟨(hp.2.2 i).1.le, hneg.le⟩

theorem sixVertexThetaDerivativeDenominator_neg_right
    (c x y : Real) :
    sixVertexThetaDerivativeDenominator c x (-y) =
      sixVertexThetaDerivativeDenominator c (-x) y := by
  unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
  rw [Real.cos_neg, Real.cos_neg, Real.sin_neg, Real.sin_neg]
  ring


end
end StatMech.FrontierD
