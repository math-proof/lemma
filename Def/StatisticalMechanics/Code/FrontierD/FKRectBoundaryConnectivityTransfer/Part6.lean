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
import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part3
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectLayerInitialRole : Fin 3 := ⟨0, by omega⟩

def fkRectLayerOldRole : Fin 3 := ⟨1, by omega⟩

def fkRectLayerNewRole : Fin 3 := ⟨2, by omega⟩


def fkRectLayerInputEmbed {W : Nat} (u : Bool × Fin W) :
    FKRectLayerVertex W :=
  (if u.1 then fkRectLayerOldRole else fkRectLayerInitialRole, u.2)


def fkRectLayerOutputEmbed {W : Nat} (u : Bool × Fin W) :
    FKRectLayerVertex W :=
  (if u.1 then fkRectLayerNewRole else fkRectLayerInitialRole, u.2)

end
end StatMech.FrontierD
