module
public import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.CrossProductExistence
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section8
public import Def.v1.Atlas.AlgebraicTopologyI.code.CrossProductExistence.Part3
public import Instance.v1.Atlas.AlgebraicTopologyI.code.Section8.Part3
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section7.Part2
open ExactSequence


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section7.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace HomologyCrossProduct

/-- Singular chains of a topological space `X` packaged as an
`IntChainComplex`: in degree `n` the group is `SingularChains n.toNat X`, with
differential `singularIntBoundary X n`, vanishing in negative degrees. -/
noncomputable def singularIntComplex
    (X : Type) [TopologicalSpace X] : ExactSequence.IntChainComplex where
  X n := AlgebraicTopologyI.SingularChains n.toNat X
  instAddCommGroup _ := inferInstance
  d n := singularIntBoundary X n
  d_comp_d n := singularIntBoundary_comp X n


end HomologyCrossProduct
