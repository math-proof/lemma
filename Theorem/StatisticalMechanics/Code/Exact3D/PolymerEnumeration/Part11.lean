/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part13


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

@[simp] theorem translateLocalCoordinate_support {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d) :
    (translateLocalCoordinate c v).support = c.support.translate v :=
  rfl

@[simp] theorem translateLocalCoordinate_degree {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d) :
    (translateLocalCoordinate c v).degree = c.degree :=
  rfl

@[simp] theorem translateLocalCoordinate_range {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d) :
    (translateLocalCoordinate c v).range = c.range :=
  rfl

@[simp] theorem translateLocalCoordinate_symmetry {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d) :
    (translateLocalCoordinate c v).symmetry = c.symmetry :=
  rfl

@[simp] theorem translateLocalCoordinate_translationQuotiented {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d) :
    (translateLocalCoordinate c v).symmetry.translationQuotiented =
      c.symmetry.translationQuotiented :=
  rfl

@[simp] theorem translateLocalCoordinate_cubicQuotiented {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d) :
    (translateLocalCoordinate c v).symmetry.cubicQuotiented =
      c.symmetry.cubicQuotiented :=
  rfl

@[simp] theorem translateLocalCoordinate_spinFlipEven {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d) :
    (translateLocalCoordinate c v).symmetry.spinFlipEven =
      c.symmetry.spinFlipEven :=
  rfl

@[simp] theorem translateLocalCoordinate_zero {d : ℕ}
    (c : LocalPolymerCoordinate d) :
    translateLocalCoordinate c (0 : Site d) = c := by
  cases c
  simp [translateLocalCoordinate]

@[simp] theorem translateLocalCoordinate_translate {d : ℕ}
    (c : LocalPolymerCoordinate d) (v w : Site d) :
    translateLocalCoordinate (translateLocalCoordinate c v) w =
      translateLocalCoordinate c (v + w) := by
  cases c
  simp [translateLocalCoordinate]

@[simp] theorem translateLocalCoordinate_support_card {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d) :
    (translateLocalCoordinate c v).support.carrier.card =
      c.support.carrier.card := by
  simp [translateLocalCoordinate]


theorem translateLocalCoordinate_coordinateDiameterBound {d R : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (hdiam : c.support.coordinateDiameterBound R) :
    (translateLocalCoordinate c v).support.coordinateDiameterBound R := by
  simpa [translateLocalCoordinate] using
    PolymerSupport.coordinateDiameterBound_translate (P := c.support)
      (v := v) hdiam


end BoundedPolymerCase
end
end Exact3D
end StatMech
