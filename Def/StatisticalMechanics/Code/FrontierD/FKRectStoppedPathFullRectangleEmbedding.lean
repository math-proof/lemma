/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectStoppedPathFullRectangleEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectLocalBoxEmbedding.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectStoppedPathTwoChannelAdapter
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingBlockSource.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStoppedConditionalLaw.Part2
open SimpleGraph


namespace StatMech.FrontierD

open StatMech StatMech.Lattice

open StatMech.Universality

noncomputable section

def rlcConnectorFullRectangleGraph (scale : Nat) :
    SimpleGraph (RlcConnectorVertex (scale : Int)) where
  Adj x y := (hypercubicLattice 2).Adj (x : Site 2) (y : Site 2)
  symm := by
    constructor
    intro x y hxy
    exact hxy.symm
  loopless := by
    constructor
    intro x hxx
    exact hxx.ne rfl

end
end StatMech.FrontierD
