/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CurveMorphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open AlgebraicGeometry CategoryTheory TopologicalSpace Order Set

/-- A smooth projective curve: an integral nonempty scheme of topological Krull dimension $1$ such that every morphism out of it is universally closed (encoding properness/completeness). -/
class SmoothProjectiveCurve (C : Scheme) : Prop where
  isIntegral : AlgebraicGeometry.IsIntegral C
  krullDim_eq : topologicalKrullDim C = 1
  nonempty : Nonempty C
  morphism_universallyClosed : ∀ {Y : Scheme} (f : C ⟶ Y), UniversallyClosed f


attribute [instance] SmoothProjectiveCurve.isIntegral SmoothProjectiveCurve.nonempty

/-- Extension theorem: every rational map from a smooth projective curve $C$ to a variety $V$ extends uniquely to a morphism $C \to V$. -/
def IsConstantMorphism {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  ∃ y : Y, ∀ x : X, f.base x = y
