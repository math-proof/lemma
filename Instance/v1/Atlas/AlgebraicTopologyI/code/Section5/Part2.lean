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
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part2
@[expose] public section

open CategoryTheory

universe u₀


namespace HomotopyCategory

namespace HoTop

/-- An object of `HoTop` may be coerced to its underlying type. -/
instance : CoeSort HoTop.{u₀} (Type u₀) := ⟨fun X => X.carrier⟩

/-- The topology on the underlying type of an object of `HoTop`. -/
instance (X : HoTop.{u₀}) : TopologicalSpace X := X.str

end HoTop
end HomotopyCategory
