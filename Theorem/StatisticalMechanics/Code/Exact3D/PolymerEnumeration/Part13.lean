/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part15


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

@[simp] theorem reflectLocalCoordinate_support {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d) :
    (reflectLocalCoordinate c ε).support = c.support.reflectCoordinates ε :=
  rfl

@[simp] theorem reflectLocalCoordinate_degree {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d) :
    (reflectLocalCoordinate c ε).degree = c.degree :=
  rfl

@[simp] theorem reflectLocalCoordinate_range {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d) :
    (reflectLocalCoordinate c ε).range = c.range :=
  rfl

@[simp] theorem reflectLocalCoordinate_symmetry {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d) :
    (reflectLocalCoordinate c ε).symmetry = c.symmetry :=
  rfl

@[simp] theorem reflectLocalCoordinate_translationQuotiented {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d) :
    (reflectLocalCoordinate c ε).symmetry.translationQuotiented =
      c.symmetry.translationQuotiented :=
  rfl

@[simp] theorem reflectLocalCoordinate_cubicQuotiented {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d) :
    (reflectLocalCoordinate c ε).symmetry.cubicQuotiented =
      c.symmetry.cubicQuotiented :=
  rfl

@[simp] theorem reflectLocalCoordinate_spinFlipEven {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d) :
    (reflectLocalCoordinate c ε).symmetry.spinFlipEven =
      c.symmetry.spinFlipEven :=
  rfl

@[simp] theorem reflectLocalCoordinate_false {d : ℕ}
    (c : LocalPolymerCoordinate d) :
    reflectLocalCoordinate c (fun _ : Fin d => false) = c := by
  cases c
  simp [reflectLocalCoordinate]

@[simp] theorem reflectLocalCoordinate_reflectLocalCoordinate {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε δ : PolymerSupport.CoordinateReflection d) :
    reflectLocalCoordinate (reflectLocalCoordinate c ε) δ =
      reflectLocalCoordinate c (fun i => Bool.xor (ε i) (δ i)) := by
  cases c
  simp [reflectLocalCoordinate]

@[simp] theorem reflectLocalCoordinate_support_card {d : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d) :
    (reflectLocalCoordinate c ε).support.carrier.card =
      c.support.carrier.card := by
  simp [reflectLocalCoordinate]


theorem reflectLocalCoordinate_coordinateDiameterBound {d R : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d)
    (hdiam : c.support.coordinateDiameterBound R) :
    (reflectLocalCoordinate c ε).support.coordinateDiameterBound R := by
  simpa [reflectLocalCoordinate] using
    PolymerSupport.coordinateDiameterBound_reflectCoordinates
      (P := c.support) ε hdiam


theorem reflectLocalCoordinate_containedInBox {d R : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d)
    (hbox : c.support.containedInBox R) :
    (reflectLocalCoordinate c ε).support.containedInBox R := by
  simpa [reflectLocalCoordinate] using
    PolymerSupport.containedInBox_reflectCoordinates
      (P := c.support) ε hbox


end BoundedPolymerCase
end
end Exact3D
end StatMech
