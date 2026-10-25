/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part43


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

theorem classifyByMinimalCubicStableKey_eq_of_equivalent
    {d R maxDegree maxRange : ℕ}
    {c c' : BoundedPolymerCase d R maxDegree maxRange}
    (h : cubicEquivalent c c') :
    classifyByMinimalCubicStableKey c =
      classifyByMinimalCubicStableKey c' := by
  exact congrArg minimalCubicStableKey (Quotient.sound h)


theorem classifyByMinimalCubicStableKey_ofLocalCoordinate_cubicTransform
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d)
    (hbox : c.support.containedInBox R)
    (hbox' :
      (cubicTransformLocalCoordinate c v σ ε).support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    classifyByMinimalCubicStableKey
        (ofLocalCoordinate c hbox hdegree hrange) =
      classifyByMinimalCubicStableKey
        (ofLocalCoordinate (cubicTransformLocalCoordinate c v σ ε)
          hbox' (by simpa using hdegree) (by simpa using hrange)) := by
  exact classifyByMinimalCubicStableKey_eq_of_equivalent
    (ofLocalCoordinate_cubicTransformLocalCoordinate_cubicEquivalent
      c v σ ε hbox hbox' hdegree hrange)


theorem classifyByMinimalCubicStableKey_ofLocalCoordinate_permute
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d))
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    classifyByMinimalCubicStableKey
        (ofLocalCoordinate c hbox hdegree hrange) =
      classifyByMinimalCubicStableKey
        (ofLocalCoordinate (permuteLocalCoordinate c σ)
          (permuteLocalCoordinate_containedInBox c σ hbox)
          (by simpa using hdegree) (by simpa using hrange)) := by
  exact classifyByMinimalCubicStableKey_eq_of_equivalent
    (ofLocalCoordinate_permuteLocalCoordinate_cubicEquivalent
      c σ hbox hdegree hrange)


theorem classifyByMinimalCubicStableKey_ofLocalCoordinate_reflect
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    classifyByMinimalCubicStableKey
        (ofLocalCoordinate c hbox hdegree hrange) =
      classifyByMinimalCubicStableKey
        (ofLocalCoordinate (reflectLocalCoordinate c ε)
          (reflectLocalCoordinate_containedInBox c ε hbox)
          (by simpa using hdegree) (by simpa using hrange)) := by
  exact classifyByMinimalCubicStableKey_eq_of_equivalent
    (ofLocalCoordinate_reflectLocalCoordinate_cubicEquivalent
      c ε hbox hdegree hrange)


end BoundedPolymerCase
end
end Exact3D
end StatMech
