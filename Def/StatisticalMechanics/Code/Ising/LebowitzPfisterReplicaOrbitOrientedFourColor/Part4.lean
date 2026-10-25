/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitOrientedFourColor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSplitTag.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
open Finset


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaDecoratedOrbitAtomEquivOrientedFourColor
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaDecoratedOrbitAtom G sites A B q ≃
      LPReplicaOrientedFourColorAtom G sites A B q where
  toFun z := ⟨z.1.1, z.1.2.1,
    ((z.2.1, z.2.2), (z.1.2.2.1, z.1.2.2.2))⟩
  invFun z := ⟨⟨z.1, ⟨z.2.1, (z.2.2.2.1, z.2.2.2.2)⟩⟩,
    (z.2.2.1.1, z.2.2.1.2)⟩
  left_inv := by intro z; rfl
  right_inv := by intro z; rfl


end
end StatMech.Ising
