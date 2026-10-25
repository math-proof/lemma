/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic.Part8
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexEvenSymmetricLiftLinearMap (m : Nat) :
    (Fin m → Real) →ₗ[Real] (Fin (m + m) → Real) where
  toFun q := Fin.addCases (fun i => -q i.rev) q
  map_add' q r := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [add_comm]
  map_smul' a q := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp


def sixVertexEvenSymmetricLift (m : Nat) :
    (Fin m → Real) →L[Real] (Fin (m + m) → Real) :=
  (sixVertexEvenSymmetricLiftLinearMap m).toContinuousLinearMap

end
end StatMech.FrontierD
