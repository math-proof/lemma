/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Isometries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.AlgebraNotes.code.Isometries
open scoped EuclideanSpace


noncomputable section

namespace Isometries

def linearDet (f : Plane ≃ᵃⁱ[ℝ] Plane) : ℝ :=
  LinearMap.det (f.linear.toLinearMap)

def IsTranslation (f : Plane ≃ᵃⁱ[ℝ] Plane) : Prop :=
  ∃ v : Plane, ∀ x : Plane, f x = v +ᵥ x

def IsRotation (f : Plane ≃ᵃⁱ[ℝ] Plane) : Prop :=
  ∃ p : Plane, f p = p ∧ linearDet f = 1 ∧ ¬IsTranslation f

def IsReflection (f : Plane ≃ᵃⁱ[ℝ] Plane) : Prop :=
  ∃ L : AffineSubspace ℝ Plane,
    Module.finrank ℝ L.direction = 1 ∧
    (∀ x : Plane, x ∈ L → f x = x) ∧
    linearDet f = -1

def IsGlideReflection (f : Plane ≃ᵃⁱ[ℝ] Plane) : Prop :=
  linearDet f = -1 ∧
    ∃ (L : AffineSubspace ℝ Plane),
      Module.finrank ℝ L.direction = 1 ∧
        ∃ (v : Plane), v ∈ L.direction ∧ v ≠ 0 ∧
          ∀ x ∈ L, (f x : Plane) = v +ᵥ x

end Isometries
end
