/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part2

@[expose] public section


namespace AlgebraicTopologyI

open Finset AlgebraicTopology CategoryTheory

/-- An integer-graded chain complex of abelian groups. -/
abbrev ChainComplexOfAbelianGroups := ChainComplex AddCommGrpCat ℤ

end AlgebraicTopologyI
