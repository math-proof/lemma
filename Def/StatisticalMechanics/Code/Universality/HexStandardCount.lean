module
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralConnEndgame
public import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStandardCount.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Filter HexWalk Topology

open scoped Real Topology

noncomputable section

def hexRootedVertices (h : ℤ) (ts : List ℤ) : List ℂ :=
  verticesAux (-halfStep h) h ts

end
end StatMech.Universality
