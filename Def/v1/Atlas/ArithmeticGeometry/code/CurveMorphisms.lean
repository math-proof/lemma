/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CurveMorphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Class.v1.Atlas.ArithmeticGeometry.code.CurveMorphisms
open AlgebraicGeometry CategoryTheory TopologicalSpace Order Set

attribute [instance] SmoothProjectiveCurve.isIntegral SmoothProjectiveCurve.nonempty


/-- Extension theorem: every rational map from a smooth projective curve $C$ to a variety $V$ extends uniquely to a morphism $C \to V$. -/
def IsConstantMorphism {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  ∃ y : Y, ∀ x : X, f.base x = y

