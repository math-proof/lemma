/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeFormula.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.RamificationInertia.Basic
set_option maxHeartbeats 800000

open Ideal Module


/-- Abstract type-class data attached to a complete smooth curve `Spec A`, recording the
degree of its canonical divisor. -/
class CompleteSmoothCurve (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A] where
  degCanonical : ℤ

