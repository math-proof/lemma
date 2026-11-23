/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.FreeAbelianGroup
public import Instance.v1.Atlas.AlgebraicTopologyI.code.Section15
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section15
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section10
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part24
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.Algebra.Category.Grp.Abelian
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section16.Part2
open AlgebraicTopology CategoryTheory Limits AlgebraicTopologyI


public noncomputable section

namespace CWComplex.SkeletonHomology

namespace CWHomology

/-- The identification of `H_n(X_{n+1})` with the cokernel of the connecting map (the
"H" of the left-homology data of the skeleton short complex). -/
structure IsCellularMap
    {X : Type} {Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : C(X, Y)) : Prop where
  mapsTo_skeleton : ∀ (n : ℕ),
    Set.MapsTo f (CWComplex.skeleton X n :) (CWComplex.skeleton Y n :)

end CWHomology
end CWComplex.SkeletonHomology
end
