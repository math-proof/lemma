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


