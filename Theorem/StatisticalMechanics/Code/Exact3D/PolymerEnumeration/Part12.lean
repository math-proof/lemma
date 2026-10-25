/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part14


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

@[simp] theorem permuteLocalCoordinate_support {d : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d)) :
    (permuteLocalCoordinate c σ).support = c.support.permuteCoordinates σ :=
  rfl

@[simp] theorem permuteLocalCoordinate_degree {d : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d)) :
    (permuteLocalCoordinate c σ).degree = c.degree :=
  rfl

@[simp] theorem permuteLocalCoordinate_range {d : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d)) :
    (permuteLocalCoordinate c σ).range = c.range :=
  rfl

@[simp] theorem permuteLocalCoordinate_symmetry {d : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d)) :
    (permuteLocalCoordinate c σ).symmetry = c.symmetry :=
  rfl

@[simp] theorem permuteLocalCoordinate_translationQuotiented {d : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d)) :
    (permuteLocalCoordinate c σ).symmetry.translationQuotiented =
      c.symmetry.translationQuotiented :=
  rfl

@[simp] theorem permuteLocalCoordinate_cubicQuotiented {d : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d)) :
    (permuteLocalCoordinate c σ).symmetry.cubicQuotiented =
      c.symmetry.cubicQuotiented :=
  rfl

@[simp] theorem permuteLocalCoordinate_spinFlipEven {d : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d)) :
    (permuteLocalCoordinate c σ).symmetry.spinFlipEven =
      c.symmetry.spinFlipEven :=
  rfl

@[simp] theorem permuteLocalCoordinate_refl {d : ℕ}
    (c : LocalPolymerCoordinate d) :
    permuteLocalCoordinate c (Equiv.refl (Fin d)) = c := by
  cases c
  simp [permuteLocalCoordinate]

@[simp] theorem permuteLocalCoordinate_trans {d : ℕ}
    (c : LocalPolymerCoordinate d) (σ τ : Equiv.Perm (Fin d)) :
    permuteLocalCoordinate (permuteLocalCoordinate c σ) τ =
      permuteLocalCoordinate c (σ.trans τ) := by
  cases c
  simp [permuteLocalCoordinate]

@[simp] theorem permuteLocalCoordinate_support_card {d : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d)) :
    (permuteLocalCoordinate c σ).support.carrier.card =
      c.support.carrier.card := by
  simp [permuteLocalCoordinate]


theorem permuteLocalCoordinate_coordinateDiameterBound {d R : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d))
    (hdiam : c.support.coordinateDiameterBound R) :
    (permuteLocalCoordinate c σ).support.coordinateDiameterBound R := by
  simpa [permuteLocalCoordinate] using
    PolymerSupport.coordinateDiameterBound_permuteCoordinates
      (P := c.support) σ hdiam


theorem permuteLocalCoordinate_containedInBox {d R : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d))
    (hbox : c.support.containedInBox R) :
    (permuteLocalCoordinate c σ).support.containedInBox R := by
  simpa [permuteLocalCoordinate] using
    PolymerSupport.containedInBox_permuteCoordinates
      (P := c.support) σ hbox


end BoundedPolymerCase
end
end Exact3D
end StatMech
