/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitOrientedFourColor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSplitTag.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor
open Finset


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaRowTagEquivFin4 : LPReplicaRowTag ≃ Fin 4 where
  toFun
    | (false, false) => 0
    | (false, true) => 1
    | (true, false) => 2
    | (true, true) => 3
  invFun x :=
    if x = 0 then (false, false)
    else if x = 1 then (false, true)
    else if x = 2 then (true, false)
    else (true, true)
  left_inv := by
    rintro ⟨r, c⟩
    cases r <;> cases c <;> rfl
  right_inv := by
    intro x
    fin_cases x <;> rfl


def lpReplicaTagFourColor
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    ↑(Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) m)) ->
      Fin 4 :=
  fun c => lpReplicaRowTagEquivFin4 (tag c.1)

end
end StatMech.Ising
