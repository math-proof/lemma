module
public import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
public import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
public import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part17


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

def coordinatePermutationEquivalent {d R maxDegree maxRange : ℕ}
    (c c' : BoundedPolymerCase d R maxDegree maxRange) : Prop :=
  c.degree = c'.degree ∧ c.range = c'.range ∧
    ∃ σ : Equiv.Perm (Fin d),
      c'.toPolymerSupport = c.toPolymerSupport.permuteCoordinates σ

end BoundedPolymerCase
end
end Exact3D
end StatMech
