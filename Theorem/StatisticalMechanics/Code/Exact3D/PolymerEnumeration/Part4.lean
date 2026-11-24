module
public import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
public import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
public import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedSite

theorem coordinateList_injective {d R : ℕ} :
    Function.Injective (@coordinateList d R) := by
  intro x y h
  exact Subtype.ext (List.ofFn_inj.mp h)


end BoundedSite
end
end Exact3D
end StatMech
