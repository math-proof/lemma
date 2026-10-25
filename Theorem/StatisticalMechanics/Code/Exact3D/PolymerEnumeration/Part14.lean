/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part16


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

@[simp] theorem cubicTransformLocalCoordinate_support {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d) :
    (cubicTransformLocalCoordinate c v σ ε).support =
      c.support.cubicTransform v σ ε :=
  rfl

@[simp] theorem cubicTransformLocalCoordinate_degree {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d) :
    (cubicTransformLocalCoordinate c v σ ε).degree = c.degree :=
  rfl

@[simp] theorem cubicTransformLocalCoordinate_range {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d) :
    (cubicTransformLocalCoordinate c v σ ε).range = c.range :=
  rfl

@[simp] theorem cubicTransformLocalCoordinate_symmetry {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d) :
    (cubicTransformLocalCoordinate c v σ ε).symmetry = c.symmetry :=
  rfl

@[simp] theorem cubicTransformLocalCoordinate_translationQuotiented {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d) :
    (cubicTransformLocalCoordinate c v σ ε).symmetry.translationQuotiented =
      c.symmetry.translationQuotiented :=
  rfl

@[simp] theorem cubicTransformLocalCoordinate_cubicQuotiented {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d) :
    (cubicTransformLocalCoordinate c v σ ε).symmetry.cubicQuotiented =
      c.symmetry.cubicQuotiented :=
  rfl

@[simp] theorem cubicTransformLocalCoordinate_spinFlipEven {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d) :
    (cubicTransformLocalCoordinate c v σ ε).symmetry.spinFlipEven =
      c.symmetry.spinFlipEven :=
  rfl

@[simp] theorem cubicTransformLocalCoordinate_identity {d : ℕ}
    (c : LocalPolymerCoordinate d) :
    cubicTransformLocalCoordinate c (0 : Site d) (Equiv.refl (Fin d))
      (fun _ : Fin d => false) = c := by
  cases c
  simp [cubicTransformLocalCoordinate]

@[simp] theorem cubicTransformLocalCoordinate_cubicTransform {d : ℕ}
    (c : LocalPolymerCoordinate d) (v w : Site d)
    (σ τ : Equiv.Perm (Fin d))
    (ε δ : PolymerSupport.CoordinateReflection d) :
    cubicTransformLocalCoordinate
        (cubicTransformLocalCoordinate c v σ ε) w τ δ =
      cubicTransformLocalCoordinate c
        (PolymerSupport.reflectCoordinatesSite δ
          (PolymerSupport.permuteCoordinatesSite τ v) + w)
        (σ.trans τ) (fun i => Bool.xor (ε (τ.symm i)) (δ i)) := by
  cases c
  simp [cubicTransformLocalCoordinate]

@[simp] theorem cubicTransformLocalCoordinate_support_card {d : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d) :
    (cubicTransformLocalCoordinate c v σ ε).support.carrier.card =
      c.support.carrier.card := by
  simp [cubicTransformLocalCoordinate]


theorem cubicTransformLocalCoordinate_coordinateDiameterBound {d R : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d)
    (hdiam : c.support.coordinateDiameterBound R) :
    (cubicTransformLocalCoordinate c v σ ε).support.coordinateDiameterBound R := by
  simpa [cubicTransformLocalCoordinate] using
    PolymerSupport.coordinateDiameterBound_cubicTransform
      (P := c.support) (v := v) σ ε hdiam


theorem cubicTransformLocalCoordinate_containedInBox {d R S : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d)
    (hbox : c.support.containedInBox R)
    (hv : PolymerSupport.coordinateRadiusBound S v) :
    (cubicTransformLocalCoordinate c v σ ε).support.containedInBox
      (R + S) := by
  simpa [cubicTransformLocalCoordinate] using
    PolymerSupport.containedInBox_cubicTransform
      (P := c.support) (v := v) σ ε hbox hv


end BoundedPolymerCase
end
end Exact3D
end StatMech
