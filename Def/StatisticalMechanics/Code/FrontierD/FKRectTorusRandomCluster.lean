/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
import Instance.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster
open scoped BigOperators


namespace StatMech.FrontierD

noncomputable section

def fkRectOpenEdgeCount (R : FKRectTorus) (omega : R.Configuration) : Nat :=
  (Finset.univ.filter fun a : R.EdgeIndex => omega a = true).card


def fkRectNumClusters (R : FKRectTorus) (omega : R.Configuration) : Nat :=
  Fintype.card (fkRectOpenGraph R omega).ConnectedComponent


def fkRectEdgeProduct (R : FKRectTorus) (p : Real)
    (omega : R.Configuration) : Real :=
  ∏ a : R.EdgeIndex, if omega a then p else 1 - p


def fkRectRandomClusterWeight (R : FKRectTorus) (p q : Real)
    (omega : R.Configuration) : Real :=
  fkRectEdgeProduct R p omega * q ^ fkRectNumClusters R omega


def fkRectRandomClusterZ (R : FKRectTorus) (p q : Real) : Real :=
  ∑ omega : R.Configuration, fkRectRandomClusterWeight R p q omega


def fkRectCriticalP (q : Real) : Real :=
  Real.sqrt q / (1 + Real.sqrt q)

end
end StatMech.FrontierD
