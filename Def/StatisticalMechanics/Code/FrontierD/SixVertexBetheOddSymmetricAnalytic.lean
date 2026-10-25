/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricAnalytic.Part4
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexOddSymmetricLiftLinearMap (m : Nat) :
    (Fin m → Real) →ₗ[Real] (Fin ((m + 1) + m) → Real) where
  toFun q := Fin.addCases
    (Fin.lastCases 0 (fun i => -q i.rev)) q
  map_add' q r := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j
    · refine Fin.lastCases ?_ ?_ j
      · simp
      · intro k
        simp [add_comm]
    · simp
  map_smul' a q := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j
    · refine Fin.lastCases ?_ ?_ j
      · simp
      · intro k
        simp
    · simp

def sixVertexOddSymmetricLift (m : Nat) :
    (Fin m → Real) →L[Real] (Fin ((m + 1) + m) → Real) :=
  (sixVertexOddSymmetricLiftLinearMap m).toContinuousLinearMap

def sixVertexOddNegativeIndex (m : Nat) (j : Fin m) : Fin ((m + 1) + m) :=
  Fin.castAdd m j.castSucc

def sixVertexOddCentralIndex (m : Nat) : Fin ((m + 1) + m) :=
  Fin.castAdd m (Fin.last m)

def sixVertexOddPositiveIndex (m : Nat) (j : Fin m) : Fin ((m + 1) + m) :=
  Fin.natAdd (m + 1) j

end
end StatMech.FrontierD
