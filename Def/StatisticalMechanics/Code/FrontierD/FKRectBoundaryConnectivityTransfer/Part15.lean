/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Instance.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part3
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectStripInitial {W : Nat} : (n : Nat) -> Fin W -> FKRectStripVertex W n
  | 0 => id
  | n + 1 => Sum.inl ∘ fkRectStripInitial n


def fkRectStripCurrent {W : Nat} : (n : Nat) -> Fin W -> FKRectStripVertex W n
  | 0 => id
  | _ + 1 => Sum.inr


def fkRectStripBoundary {W : Nat} (n : Nat) :
    Bool × Fin W -> FKRectStripVertex W n := fun u =>
  if u.1 then fkRectStripCurrent n u.2 else fkRectStripInitial n u.2

end
end StatMech.FrontierD
