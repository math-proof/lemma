module
public import Theorem.StatisticalMechanics.Code.Universality.HexContourDecomp.Part2
public import Theorem.StatisticalMechanics.Code.Universality.HexVertexBoundConcrete.Part4
public import Def.StatisticalMechanics.Code.Universality.HexBoundaryUncond


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryUncond.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex

open scoped BigOperators


@[simp]
theorem hexUncondDomain_interiorVertices (a : ℂ) (h0 : ℤ) :
    (hexUncondDomain a h0).interiorVertices = {0} := rfl


end StatMech.Universality
