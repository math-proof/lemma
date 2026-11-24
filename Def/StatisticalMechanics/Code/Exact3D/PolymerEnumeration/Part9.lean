module
public import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
public import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
public import Instance.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part4


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

namespace BoundedPolymerCase

noncomputable def boundedSupportOf {d R : ℕ} (P : PolymerSupport d)
    (hP : P.containedInBox R) : Finset (BoundedSite d R) :=
  P.carrier.attach.image fun x => ⟨x.1, hP x.1 (by simp)⟩


end BoundedPolymerCase
end
end Exact3D
end StatMech
