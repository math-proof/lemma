/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCylinderTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PositiveTransferObservable
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.IsingCylinderTransfer.Part2
open Finset Matrix Filter Topology
open scoped BigOperators


namespace StatMech.Ising

noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]


def isingCylinderPartition
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real)
    (leftBoundary rightBoundary : ConfigSpace W -> Real) (n : Nat) : Real :=
  let A := isingCylinderTransfer E J h Jvertical
  let a := isingCylinderBoundaryVector E J h leftBoundary
  let ell := isingCylinderBoundaryVector E J h rightBoundary
  ∑ s, ell s * ((A ^ n) *ᵥ a) s


def isingCylinderEndpointMean
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real)
    (leftBoundary rightBoundary : ConfigSpace W -> Real)
    (obs : ConfigSpace W -> Real) (n : Nat) : Real :=
  let A := isingCylinderTransfer E J h Jvertical
  let a := isingCylinderBoundaryVector E J h leftBoundary
  let ell := isingCylinderBoundaryVector E J h rightBoundary
  (∑ s, ell s * obs s * ((A ^ n) *ᵥ a) s) /
    ∑ s, ell s * ((A ^ n) *ᵥ a) s


end
end StatMech.Ising
