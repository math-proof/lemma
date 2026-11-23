/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
public import Mathlib.Algebra.Homology.AlternatingConst
public import Def.v1.Atlas.AlgebraicTopologyI.code.ContractibleHomology.Part2
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.ContractibleHomology
public import Instance.v1.Atlas.AlgebraicTopologyI.code.Section5.Part2

@[expose] public section

open CategoryTheory

universe u₀


namespace HomotopyCategory

namespace HoTop

/-- Bundle a topological space `X` as an object of the homotopy category `HoTop`. -/
def of (X : Type u₀) [TopologicalSpace X] : HoTop := TopCat.of X

end HoTop
end HomotopyCategory
