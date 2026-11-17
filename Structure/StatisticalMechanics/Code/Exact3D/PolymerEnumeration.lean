/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
public import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
public import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part5


namespace StatMech

namespace Exact3D

open StatMech.Lattice

public noncomputable section

structure BoundedPolymerCase (d R maxDegree maxRange : ℕ) where
  support : Finset (BoundedSite d R)
  degree : Fin (maxDegree + 1)
  range : Fin (maxRange + 1)
deriving DecidableEq, Fintype

end
end Exact3D
end StatMech
