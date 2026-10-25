/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryProfile.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABMeanfieldGhost
import Theorem.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.ABBoundaryProfile
open Finset Set SimpleGraph


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent Lattice


def abbCoupling (d n : Nat) : Sym2 (sctBox d n) -> Real := fun _ => 1


noncomputable def abbMag (d n : Nat) (beta h : Real) : Real :=
  abmgTargetMag (sctBoxGraph d n) (abbCoupling d n)
    (sctBoxOrigin d n) (abbTarget d n) beta h


noncomputable def abbPhi (d n : Nat) (beta h : Real)
    (S : Finset (Option (sctBox d n))) : Real :=
  abmgTargetPhi (sctBoxGraph d n) (abbCoupling d n)
    (sctBoxOrigin d n) (abbTarget d n) beta h S


end Sharpness
end StatMech
